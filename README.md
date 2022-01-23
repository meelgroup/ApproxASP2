## ApproxASP
Approximate counting of answer sets via clingo. 

### Installation
- Install clingo following [this link](https://github.com/meelgroup/ApproxASP2/blob/master/INSTALL.md)
- execute `cd libgauss`
- then `make`. After successful compile, the `approxasp` is the target binary.

### Running ApproxASP
- With independent support
`./approxasp --useind <independent support file> --asp <asp file>`

- Without independent support
`./approxasp --asp <asp file>`