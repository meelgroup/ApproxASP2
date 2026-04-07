## ApproxASP
Approximate counting of answer sets via answer set solver clingo. The related publication: [ApproxASP](https://ojs.aaai.org/index.php/AAAI/article/view/20518)


### Dependencies
You need to install `bison` and `re2c`. It is required by clingo.
```
sudo apt-get install bison
sudo apt-get install re2c
```

### Building
Execute the following:

```
mkdir build && cd build
cmake -DCLINGO_BUILD_SHARED=ON ..
make -j12
```
You should now have the binary `appproxasp` in your directory

### Running ApproxASP
- With independent support
`./approxasp --useind <independent support file> --asp <asp file>`

- Without independent support
`./approxasp --asp <asp file>`

### Benchmark and binaries
The benchmark used in our AAAI 2022 paper evaluation is available [here](https://zenodo.org/records/19316194).

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

