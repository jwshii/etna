import boto3
import os

bucket_name = "pldi"
s3 = boto3.resource('s3')

os.mkdir("downloads")
os.mkdir("downloads/FuzzerChecker")
os.mkdir("downloads/ShallowVsDeep-Coq")
os.mkdir("downloads/ShallowVsDeep-Racket")


bucket = s3.Bucket(bucket_name)
for obj in bucket.objects.all():
    key = obj.key
    print("Downloading", key)
    bucket.download_file(key, "downloads/" + key)
