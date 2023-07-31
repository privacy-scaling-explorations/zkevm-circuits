#!/bin/bash

profile="cirunner"
runner_vpc_id="vpc-05dedcb650bd24f8d"

# Get runner status
runner=$(aws ec2 describe-instances --profile $profile --filters Name=tag:Name,Values=[testool] Name=network-interface.vpc-id,Values=[$runner_vpc_id] --query "Reservations[*].Instances[*][InstanceId]" --output text | xargs)

echo "Reports: http://testool-public.s3-website.eu-central-1.amazonaws.com"
echo "Shuting down instance..."
aws ec2 stop-instances --profile $profile --instance-ids $runner

exit 0
