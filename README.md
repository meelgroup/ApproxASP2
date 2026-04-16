## ApproxASP
Approximate counting of answer sets via answer set solver clingo. The related publication: [ApproxASP](https://ojs.aaai.org/index.php/AAAI/article/view/20518)

### Clone
clone the repo with submodules:
```
git clone --recurse-submodules git@github.com:meelgroup/ApproxASP.git
```


### Dependencies
You need to install `bison` and `re2c`. It is required by clingo.
```
sudo apt-get install bison
sudo apt-get install re2c
sudo apt-get install build-essential cmake
```

### Building
Compile approxasp as follows:

```
chmod +x build.sh
./build.sh
```


### Running ApproxASP
copy `approxasp` from build: `cp build/approxasp .`

Run approxasp
- With independent support
`./approxasp --useind <independent support file> --asp <asp file>`
e.g.,
```
./approxasp --useind IS_molise.lp --asp molise.lp
```

- Without independent support
`./approxasp --asp <asp file>`
e.g.,
```
./approxasp --asp vertex-cover.lp
```

### Benchmark and Artifacts
The benchmark and artifact used in our AAAI 2022 paper evaluation is available [here](https://zenodo.org/records/19608413).

### Reference
Please cite our work if you use it:
```
@inproceedings{kabir2022approxasp,
  title={ApproxASP--a scalable approximate answer set counter},
  author={Kabir, Mohimenul and Everardo, Flavio O and Shukla, Ankit K and Hecher, Markus and Fichte, Johannes Klaus and Meel, Kuldeep S},
  booktitle={AAAI},
  volume={36},
  number={5},
  pages={5755--5764},
  year={2022}
}
```

