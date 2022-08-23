#!/bin/bash

profile="cirunner"
runner_vpc_id="vpc-8bdf97ec"

# Get runner status
runner=$(aws ec2 describe-instances --profile $profile --filters Name=tag:Name,Values=[jenkins] Name=network-interface.vpc-id,Values=[$runner_vpc_id] --query "Reservations[*].Instances[*][InstanceId]" --region us-west-2 --output text | xargs)

while true; do
    runner_status=$(aws ec2 describe-instances --profile $profile --instance-ids $runner --query "Reservations[*].Instances[*].State.[Name]" --region us-west-2 --output text)
    if [ $runner_status = "stopped" ]; then
        aws ec2 start-instances --profile $profile --instance-ids $runner --region us-west-2
        exit 0
    elif [ $runner_status = "running" ]; then
        sleep 120
        runner_status=$(aws ec2 describe-instances --profile $profile --instance-ids $runner --query "Reservations[*].Instances[*].State.[Name]" --region us-west-2 --output text)
        if [ $runner_status = "running" ]; then
            exit 0
        fi
    else
        sleep 30
    fi
done
