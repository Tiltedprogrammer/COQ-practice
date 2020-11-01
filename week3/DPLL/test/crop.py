from os import listdir
from os.path import isfile, join
import sys


if __name__ == "__main__":
    path = sys.argv[1];
    onlyfiles = [join(path,f) for f in listdir(path) if isfile(join(path, f))]
    for f in onlyfiles:
        with open(f,'r') as fr:
            with open(f"{f}-cropped",'w') as wr:
                wr.writelines(fr.readlines()[:-3])