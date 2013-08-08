CNF Translations for the Car-Sequencing Problem
=========================================

CNF encoder/decoder for car-sequencing problems from http://www.cs.st-andrews.ac.uk/~ianm/CSPLib/prob/prob001/

Version info:

```bash
./car_encode -ver
```
Help:

```bash
./car_encode -help
```

To generate models, e.g. model E3 with symmetry breaking:

```bash
./car_encode -f hard/p00.txt -e3 -sym
```

If the one needs to study the solution there is a decoder that can be used
with a generated symbol table. See the following example:

```bash
./car_encode -f easy/test.txt -e3 -symbols symbols.txt > problem.cnf
lingeling problem.cnf > solution.txt
./car_decode -symbols symbols.txt -solution solution.txt
```

which should give the output as on the CSPLib website: 

    4	  1 0 1 0 0 
    3	  0 1 0 1 0 
    2	  0 1 0 0 1 
    4	  1 0 1 0 0 
    3	  0 1 0 1 0 
    5	  1 1 0 0 0 
    1	  0 0 0 1 0 
    5	  1 1 0 0 0 
    2	  0 1 0 0 1 
    0	  1 0 1 1 0 
