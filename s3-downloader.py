import boto3
import os
import hashlib

bucket_name = "pldi"
s3 = boto3.resource('s3')

os.makedirs("downloads", exist_ok=True)
os.makedirs("downloads/FuzzerChecker", exist_ok=True)
os.makedirs("downloads/ShallowVsDeep-Coq", exist_ok=True)
os.makedirs("downloads/ShallowVsDeep-Racket", exist_ok=True)

bucket = s3.Bucket(bucket_name)
for obj in bucket.objects.all():

    if os.path.exists("downloads/" + obj.key):
        file_hash = hashlib.md5(open("downloads/" + obj.key, 'rb').read()).hexdigest()
        if file_hash == obj.e_tag[1:-1]:
            print("Skipping", obj.key)
            continue

    print("Downloading", obj.key)
    bucket.download_file(obj.key, "downloads/" + obj.key)
