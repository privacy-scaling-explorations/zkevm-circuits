#!/bin/bash
set -e
#set -x

label=$1
degree=$2

# Get the latest temp directory in the Triggerers directory
trigger_results_dir="../../../results/$label"
mkdir -p $trigger_results_dir || true

# Get the latest temp directory in the Provers home directory
prover_latest_dir=$(ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" <<EOF
ls -td -- "\$HOME"/CI_Prover_Benches/* | head -1
EOF
)

prover_target_dir="$prover_latest_dir/zkevm-circuits"
prover_results_dir="$prover_latest_dir/results"
echo $prover_target_dir

# Collect results from Prover
echo "Collecting results from $PROVER_IP:$prover_results_dir to TRIGGER_HOST:$trigger_results_dir"
scp -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP:$prover_results_dir/*proverlog $trigger_results_dir/

# Enable bash Environment Variables for Prover
ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" <<EOF
echo "PermitUserEnvironment yes" | sudo tee -a /etc/ssh/sshd_config
sudo service sshd restart
EOF
sleep 10

# Collect cpu and memory metrics
scp -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ./sadf.sh ubuntu@$PROVER_IP:~/
ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" <<EOF
BENCH_BEGIN=\$(cat /home/ubuntu/bench_begin)
echo "Bench began at \$BENCH_BEGIN"
mv /home/ubuntu/sadf.sh $prover_results_dir/
cd $prover_results_dir
./sadf.sh \$BENCH_BEGIN
EOF
scp -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP:$prover_results_dir/*.stats $trigger_results_dir/

# Prepare for and run data processing and db persistence

l=$(echo $label | tr -d '"')
circuit=$(echo $l |  awk '{print $1}')
time=$(date +%Y-%m-%d_%H-%M-%S)
test_id=$time-$circuit-$degree-Benchmark

cd $trigger_results_dir
tar -czvf ./$test_id.tar.gz ./*proverlog ./*.stats

cp ../../zkevm-circuits/.github/weeklyBenchScripts/reporting*.py .
sudo cp *proverlog /var/www/www_logs/
proverlog="http://43.130.90.57/www_logs/"$(ls -t /var/www/www_logs | head -1)
sed -i '1i BENCH-PROVER;-1;UTC;LINUX-RESTART	(64 CPU)' mem.stats
sed -i '1i BENCH-PROVER;-1;UTC;LINUX-RESTART	(64 CPU)' cpu.stats
python3 reporting_main.py  "$proverlog" "1" "$circuit" "$degree" "$test_id"

ssh -i ~/.ssh/bench.pem -o StrictHostKeyChecking=no ubuntu@$PROVER_IP "bash -s" <<EOF
sudo rm -rf $prover_results_dir
EOF

exit 0
