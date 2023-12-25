# Rational SOS - A Maple package for exact SOS decomposition.

The package implements the algorithms presented in the research paper
["Facial reduction for exact polynomial sum of squares decompositions"](https://arxiv.org/abs/1810.04215).

Official package website: [https://slaplagne.bitbucket.io/rationalSOS/](https://slaplagne.bitbucket.io/rationalSOS/)

## Getting Started

Download the full repository zip file from the Downloads menu and unzip in your working directory.

### Prerequisites

For using the software you need Maple, Matlab, and SEDUMI package installed in Matlab. 
SEDUMI package is freely available from [SEDUMI website](http://sedumi.ie.lehigh.edu/ "SEDUMI").

### Installing

No installation is needed, use the following commands in Maple to load the package, replacing the path by the path where you unzipped the file.

```
# Change to the path of the file rationalSOS.mpl
currentdir("C:/Users/User/rationalSOS");
read("rationalSOS.mpl");
with(rationalSOS);
```

Try the following example:
```
f := 10*x^4+2*x^3*y+27x^2*y^2−24*x*y^3+5*y^4;
exactSOS(f);
```

## Running the example files

Several Maple sheets are provided with the examples used in the paper and other usage examples.
Open the filed .mpl in Maple and run the code.


## Author

  **Santiago Laplagne** - *Departamento de Matemática, FCEyN, Universidad de Buenos Aires* - [Homepage](http://cms.dm.uba.ar/Members/slaplagn)

## License

The code is freely available.
