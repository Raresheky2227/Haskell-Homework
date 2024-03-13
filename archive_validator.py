import yaml
import os
import sys
from functools import reduce
from deepdiff import DeepDiff
import zipfile
import shutil
import re


def get_yaml_structure(filename: str):
    file = None
    with open(filename, "r") as stream:
        try:
            file = yaml.safe_load(stream)
        except yaml.YAMLError as exc:
            print(exc)
    return file


def get_directory_structure(rootdir: str) -> dict:
    """
    Creates a nested dictionary that represents the folder structure of rootdir
    """
    dir_hierarchy = {}
    rootdir = rootdir.rstrip(os.sep)
    start = rootdir.rfind(os.sep) + 1
    for path, dirs, files in os.walk(rootdir):
        folders = path[start:].split(os.sep)
        subdir = dict.fromkeys(files)
        parent = reduce(dict.get, folders[:-1], dir_hierarchy)
        parent[folders[-1]] = subdir
    return dir_hierarchy

def compress(d: dict) -> dict:
    if d.keys() == []:
        return None
    key = list(d.keys())[0]
    elems = []
    for k, v in d[key].items():
        if v is None:
            elems.append(k)
        else:
            elems.append(compress({k:v}))
    if len(elems) == 1:
        return {key: elems[0]}
    return {key: elems}

TEST_DIR_NAME= "test_dir"
YAML_REF_FLIE= "ref.yaml"
if __name__ == "__main__":
    args  = sys.argv
    if len(args) < 2:
        exit("[ERROR] No archive is specified")
    archive_name = args[1]
    if not re.match("^.*[.]zip$", archive_name):
        exit("[ERROR] The archive should be a .zip file")
    with zipfile.ZipFile(archive_name,"r") as zip_ref:
        zip_ref.extractall(TEST_DIR_NAME)
    yaml_structure = get_yaml_structure(YAML_REF_FLIE)
    dir_structure = compress(get_directory_structure(TEST_DIR_NAME))
    errors = DeepDiff(yaml_structure, dir_structure[TEST_DIR_NAME], ignore_order=True)
    if errors != {}:
        print(f"The archive is not properly structured: {errors}")
    else:
        print("The archive format is valid")
    shutil.rmtree(TEST_DIR_NAME)
