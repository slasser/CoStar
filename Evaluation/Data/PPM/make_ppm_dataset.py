import subprocess

if __name__ == "__main__":
    for i in range(10, 101, 1):
        subprocess.run("convert -compress none -resize {}% webb.jpg Instances/webb_{}.ppm".format(i, i), shell=True)
