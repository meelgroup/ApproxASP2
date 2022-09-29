## ApproxASP
Approximate counting of answer sets via clingo. 

### Building- execute `cd libgauss`
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
