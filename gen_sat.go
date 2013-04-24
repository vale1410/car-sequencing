package main

import (
	"bytes"
	"flag"
	"fmt"
	"io/ioutil"
	"regexp"
	"strconv"
	"strings"
)

var name = flag.String("file", "", "Path of the file specifying the car sequencing according to the CSPlib.")
var ver = flag.Bool("ver", false, "Show version info.")
var e1 = flag.Bool("e1", false, "Collection of flags: ex1, cnt, ca1, ca2, ca3, ca4, ca5, id7, id8, id9.")
var e2 = flag.Bool("e2", false, "Collection of flags: ex1, cnt, re1, re2, id7, id8, id9.")
var e3 = flag.Bool("e3", false, "Collection of flags: ex1, cnt, id6, id7, id8, id9.")
var e4 = flag.Bool("e4", false, "Collection of flags: ex1, cnt, re1, re2, id6, id7, id8, id9.")
var e5 = flag.Bool("e5", false, "Collection of flags: ex1, cnt, ca1, ca2, ca3, ca4, ca5, re1, re2, id6, id7, id8, id9.")
var ex1 = flag.Bool("ex1", false, "Adds clauses to state that in each position there is exactly one car.")
var cnt = flag.Bool("cnt", false, "Meta flag: sets id1, id2, id3, id4, id5.")
var ca1 = flag.Bool("ca1", false, "Sequential Counter for capacity constraints, type 1.")
var ca2 = flag.Bool("ca2", false, "Sequential Counter for capacity constraints, type 2.")
var ca3 = flag.Bool("ca3", false, "Sequential Counter for capacity constraints, type 3.")
var ca4 = flag.Bool("ca4", false, "Sequential Counter for capacity constraints, type 4.")
var ca5 = flag.Bool("ca5", false, "Initializes the counter to be a AtMost constraint.")
var id1 = flag.Bool("id1", false, "Sequential Counter for cardinality, clauses 1 (see paper).")
var id2 = flag.Bool("id2", false, "Sequential Counter for cardinality, clauses 2 (see paper).")
var id3 = flag.Bool("id3", false, "Sequential Counter for cardinality, clauses 3 (see paper).")
var id4 = flag.Bool("id4", false, "Sequential Counter for cardinality, clauses 4 (see paper).")
var id5 = flag.Bool("id5", false, "Initializes the counter to be a cardinality constraint.")
var id6 = flag.Bool("id6", false, "AtMostSeqCard reusing the aux variables of cardinality constraints on the demand");
var id7 = flag.Bool("id7", false, "Implications from Classes to Options.")
var id8 = flag.Bool("id8", false, "Class to Option relations, alternative 1: Completion Clause. (alternative to id9)")
var id9 = flag.Bool("id9", false, "Class to Option relations, alternative 2: class implies neg options. Adds binary"+
	" clauses (alternative to id8).")
var re1 = flag.Bool("re1", false, "Implications of options that are of the form 1/q. Adds binary clauses.")
var re2 = flag.Bool("re2", false, "Implications of options that are of the form 2/q. Adds binary clauses.")
var sym = flag.Bool("sym", false, "Order the sequence in one direction (first car has lower or equal class id than last).")
var ian = flag.Bool("ian", false, "A redundant constraint that precomputes sets of classes that need to be neighbours.")
var sbd = flag.Bool("sbd", false, "For initial grounding use simple bounds to generate counters.  (context optimization).")
var opt = flag.Int("opt", -1, "Adds optimization statement with value given. Should be used with -sbd and without -re1 -re2.")
var add = flag.Int("add", 0, "Add n dummy cars without any option. (simulates optimization).")
var debug = flag.Bool("debug", false, "Adds debug information to the cnf (symbol table and textual clauses).")

var digitRegexp = regexp.MustCompile("([0-9]+ )*[0-9]+")

var size, class_count, option_count int
var gen IdGen

func main() {
	flag.Parse()
    if *ver { 
        fmt.Println(`CNF generator for car sequencing problem from CSPLib 
Version tag: 1.0
For infos about flags use -help
Copyright (C) NICTA and Valentin Mayer-Eichberger
License GPLv2+: GNU GPL version 2 or later <http://gnu.org/licenses/gpl.html>
There is NO WARRANTY, to the extent permitted by law.`)
        return
    } 
	setFlags()
    if *name == "" { 
        *name = flag.Arg(0)
    } 
	parse(*name)
}

func setFlags() {
	t := true

	if *e1 {
		ex1 = &t
		cnt = &t
        ca1 = &t
        ca2 = &t
        ca3 = &t
        ca4 = &t
        ca5 = &t
		id7 = &t
		id8 = &t
		id9 = &t
	}

	if *e2 {
		ex1 = &t
		cnt = &t
		re1 = &t
		re2 = &t
		id7 = &t
		id8 = &t
		id9 = &t
	}

	if *e3 {
		ex1 = &t
		cnt = &t
		id6 = &t
		id7 = &t
		id8 = &t
		id9 = &t
	}

	if *e4 {
		ex1 = &t
		cnt = &t
		re1 = &t
		re2 = &t
		id6 = &t
		id7 = &t
		id8 = &t
		id9 = &t
	}

	if *e5 {
		ex1 = &t
		cnt = &t
        ca1 = &t
        ca2 = &t
        ca3 = &t
        ca4 = &t
        ca5 = &t
		re1 = &t
		re2 = &t
		id6 = &t
		id7 = &t
		id8 = &t
		id9 = &t
	}


	if *cnt {
		id1 = &t
		id2 = &t
		id3 = &t
		id4 = &t
		id5 = &t
	}
}

const (
	optionType countType = iota
	classType
	exactlyOne
	optimizationType
)

type countType int
type clause struct {
	desc     string
	literals []int
}

type CountableId struct {
	typ   countType
	index int
}

type Countable struct {
	cId      CountableId
	window   int
	capacity int
	demand   int
	lower    []int
	upper    []int
}

type PosVar struct {
	cId CountableId
	pos int
}

type CountVar struct {
	cId   CountableId
	pos   int
	count int
}

type AtMostVar struct {
	cId   CountableId
	first int
	pos   int
	count int
}

type IdGen struct {
	id          int
	countVarMap map[CountVar]int
	posVarMap   map[PosVar]int
	atMostVarMap   map[AtMostVar]int
}

func NewIdGen() {
	gen.id = 0
	gen.posVarMap = make(map[PosVar]int, size*(class_count+option_count)) //just an approximation of size of map
	gen.countVarMap = make(map[CountVar]int, size*class_count^2)  //just an approximation of size of map  
	gen.atMostVarMap = make(map[AtMostVar]int, size*class_count^2) //just an approximation of size of map
	return
}

func printClausesDIMACS(clauses []clause) {

	fmt.Printf("p cnf %v %v\n", len(gen.posVarMap)+len(gen.countVarMap)+len(gen.atMostVarMap), len(clauses))

	for _, c := range clauses {
		for _, l := range c.literals {
			fmt.Printf("%v ", l)
		}
		fmt.Printf("0\n")
	}
}

func printDebug(clauses []clause) {

	symbolTable := make([]string, len(gen.countVarMap)+len(gen.posVarMap)+len(gen.atMostVarMap)+1)

	for key, valueInt := range gen.posVarMap {
		s := ""
		switch key.cId.typ {
		case optionType:
			s = "pos(option,"
		case classType:
			s = "pos(class,"
		case exactlyOne:
			s = "pos(aux,"
		case optimizationType:
			s = "pos(opti,"
		}
		s += strconv.Itoa(key.cId.index)
		s += ","
		s += strconv.Itoa(key.pos)
		s += ")"
		symbolTable[valueInt] = s
	}

	for key, valueInt := range gen.countVarMap {
		s := ""
		switch key.cId.typ {
		case optionType:
			s = "count(option,"
		case classType:
			s = "count(class,"
		case optimizationType:
			s = "count(opti,"
		}
		s += strconv.Itoa(key.cId.index)
		s += ","
		s += strconv.Itoa(key.pos)
		s += ","
		s += strconv.Itoa(key.count)
		s += ")"
		symbolTable[valueInt] = s
	}

	for key, valueInt := range gen.atMostVarMap {
		s := ""
		switch key.cId.typ {
		case optionType:
			s = "atMost(option,"
		case classType:
			s = "atMost(class,"
		case optimizationType:
			s = "atMost(opti,"
		}
		s += strconv.Itoa(key.cId.index)
		s += ","
		s += strconv.Itoa(key.first)
		s += ","
		s += strconv.Itoa(key.pos)
		s += ","
		s += strconv.Itoa(key.count)
		s += ")"
		symbolTable[valueInt] = s
	}

	fmt.Println("c pos(Type,Id,Position).")
	fmt.Println("c count(Type,Id,Position,Count).")
	fmt.Println("c atMost(Type,Id,First,Position,Count).")
	for i, s := range symbolTable {
		fmt.Println("c", i, "\t:", s)
	}

	stat := make(map[string]int, 10)

	for _, c := range clauses {

		count, ok := stat[c.desc]
		if !ok {
			stat[c.desc] = 1
		} else {
			stat[c.desc] = count + 1
		}

		fmt.Printf("c %s ", c.desc)
		first := true
		for _, l := range c.literals {
			if !first {
				fmt.Printf(",")
			}
			first = false
			if l < 0 {
				fmt.Printf("-%s", symbolTable[-l])
			} else {
				fmt.Printf("+%s", symbolTable[l])
			}
		}
		fmt.Println(".")
	}

	all := []string{"id1",
		"id2",
		"id3",
		"id4",
		"id5",
		"id6",
		"id7",
		"id8",
		"id9",
		"ca1",
		"ca2",
		"ca3",
		"ca4",
		"ca5",
		"lt1",
		"gt1",
		"sym",
		"re1",
		"re2",
		"op0",
		"op1",
		"op2",
		"op3",
		"op4"}

	for _, key := range all {
		fmt.Printf("c %v\t: %v\t%.1f \n", key, stat[key], 100*float64(stat[key])/float64(len(clauses)))
	}
	fmt.Printf("c %v\t: %v\t%.1f \n", "tot", len(clauses), 100.0)
}

func getCountId(v CountVar) (id int) {
	id, b := gen.countVarMap[v]

	if !b {
		gen.id++
		id = gen.id
		gen.countVarMap[v] = id
	}
	return id
}

func getPosId(v PosVar) (id int) {
	id, b := gen.posVarMap[v]

	if !b {
		gen.id++
		id = gen.id
		gen.posVarMap[v] = id
	}
	return id
}

func getAtMostId(v AtMostVar) (id int) {
	id, b := gen.atMostVarMap[v]

	if !b {
		gen.id++
		id = gen.id
		gen.atMostVarMap[v] = id
	}
	return id
}

func parse(filename string) bool {
	input, err := ioutil.ReadFile(filename)

	if err != nil {
        fmt.Println("Please specifiy correct path to instance. Does not exist: ", filename)
		return false
	}

	b := bytes.NewBuffer(input)

	lines := strings.Split(b.String(), "\n")

	state := 0

	var options []Countable
	var classes []Countable
	var class2option [][]bool

	// parse stuff
	for _, l := range lines {
		numbers := strings.Split(strings.TrimSpace(l), " ")
		if digitRegexp.MatchString(numbers[0]) {
			switch state {
			case 0:
				{
					size, _ = strconv.Atoi(numbers[0])
					option_count, _ = strconv.Atoi(numbers[1])
					options = make([]Countable, option_count)
					class_count, _ = strconv.Atoi(numbers[2])
					classes = make([]Countable, class_count)
					class2option = make([][]bool, class_count)
				}
			case 1:
				{
					for i, v := range numbers {
						capacity, _ := strconv.Atoi(v)
						options[i].cId = CountableId{optionType, i}
						options[i].capacity = capacity
					}
				}
			case 2:
				{
					for i, v := range numbers {
						window, _ := strconv.Atoi(v)
						options[i].window = window
					}
				}
			default:
				{
					num, _ := strconv.Atoi(numbers[0])
					classes[num].cId = CountableId{classType, num}
					class2option[num] = make([]bool, option_count)

					// find option with lowest slope
					// to determine capacity and windows

					classes[num].capacity = 1
					classes[num].window = 1
					slope := 1.0

					for i, v := range numbers {
						if i == 1 {
							demand, _ := strconv.Atoi(v)
							classes[num].demand = demand
						} else if i > 1 {
							value, _ := strconv.Atoi(v)
							has_option := value == 1
							class2option[num][i-2] = has_option
							if has_option {
								options[i-2].demand += classes[num].demand
								slope2 := float64(options[i-2].capacity) / float64(options[i-2].window)
								if slope2 < slope {
									slope = slope2
									classes[num].capacity = options[i-2].capacity
									classes[num].window = options[i-2].window
								}
							}
						}
					}
				}
			}
			state++
		} else {
			fmt.Println("c ", l)
		}
	}

	if *add > 0 {
		cId := CountableId{classType, class_count}
		dummy := Countable{cId: cId, window: 1, capacity: 1, demand: *add}
		classes = append(classes, dummy)
		class2option = append(class2option, make([]bool, option_count))
		class_count++
		size += *add
	}

	for i := range options {
		options[i].createBounds()
	}

	for i := range classes {
		classes[i].createBounds()
	}

	NewIdGen()

	clauses := make([]clause, 0)

	//clauses 1-6 for classes
	for _, c := range classes {
        if *id1 || *id2 ||*id3 ||*id4 {
			clauses = append(clauses, createCounter(c)...)
        }
		if *id5 {
			clauses = append(clauses, createAtMostSeq5(c)...)
		}
		if *id6 {
			clauses = append(clauses, createAtMostSeq6(c)...)
		}
	}

	//clauses 1-6 for options
	for _, o := range options {
        if *ca1 || *ca2 || *ca3 || *ca4 || *ca5 {
			clauses = append(clauses, createCapacityConstraints(o)...)
        }
        if *id1 || *id2 ||*id3 ||*id4 {
			clauses = append(clauses, createCounter(o)...)
        }
		if *id5 {
			clauses = append(clauses, createAtMostSeq5(o)...)
		}
		if *id6 {
			clauses = append(clauses, createAtMostSeq6(o)...)
		}
		if *re1 {
			clauses = append(clauses, createRedundant1(o)...)
		}
		if *re2 {
			clauses = append(clauses, createRedundant2(o)...)
		}
		if *opt > 0 {
			clauses = append(clauses, createOptPositions(o)...)
			clauses = append(clauses, createOptCounter(o)...)
		}
	}

	//clauses 7 and 9
	for i := 0; i < class_count; i++ {
		for j := 0; j < option_count; j++ {
			if class2option[i][j] {
				if *id7 {
					clauses = append(clauses, createAtMostSeq7(classes[i].cId, options[j].cId)...)
				}
			} else {
				if *id9 {
					clauses = append(clauses, createAtMostSeq9(classes[i].cId, options[j].cId)...)
				}
			}
		}
	}

	//clauses 8
	if *id8 {
		for j := 0; j < option_count; j++ {

			ops := make([]CountableId, 0, class_count)

			for i := 0; i < class_count; i++ {
				if class2option[i][j] {
					k := len(ops)
					ops = ops[:k+1]
					ops[k] = classes[i].cId
				}
			}
			clauses = append(clauses, createAtMostSeq8(options[j].cId, ops)...)
		}
	}

	//clauses exactly one class per position
	if *ex1 {
		clauses = append(clauses, createExactlyOne()...)
	}

	//symmetry breaking
	if *sym {
		clauses = append(clauses, createSymmetry()...)
	}

	//fmt.Println("number of clauses: ", len(clauses))
	//fmt.Println("number of pos variables: ", len(gen.posVarMap))
	//fmt.Println("number of count variables: ", len(gen.countVarMap))

	if *ian {
		createIanConstraints(options, classes, class2option)
	}

    if len(clauses) > 0 { 
	    printClausesDIMACS(clauses)
    } 
	if *debug {
		fmt.Println("c options: ", options)
		fmt.Println("c classes: ", classes)
		fmt.Println("c class2option: ", class2option)
		printDebug(clauses)
	}

	return true
}

func createIanConstraints(options []Countable, classes []Countable, class2option [][]bool) (clauses []clause) {

	first := make([]bool, option_count, option_count)

	sets := createSubSets(0, first)

	// how many 1/2
	cap12 := make([]int, len(sets))
	// how many 1/k, k > 2
	cap1k := make([]int, len(sets))
	// how many 2/k > 2
	cap2k := make([]int, len(sets))
	demands := make([]int, len(sets))
	supplies := make([]int, len(sets))
	rest := make([]int, len(sets))

	for s, set := range sets {
		// find max capacity among options
		for j, b := range set {
			if b && options[j].window > 1 {
				if options[j].window == 2 && options[j].capacity == 1 {
					cap12[s]++
				} else if options[j].window > 2 && options[j].capacity == 1 {
					cap1k[s]++
				} else if options[j].window > 2 && options[j].capacity == 2 {
					cap2k[s]++
				}
			}
		}

		for i, class := range classes {
			alwaysfit := true
			neverfit := true
			for j, b := range set {
				if b {
					if class2option[i][j] {
						neverfit = false
					} else {
						alwaysfit = false
					}
				}
			}
			if alwaysfit {
				demands[s] += class.demand
			}
			if neverfit {
				supplies[s] += class.demand
			}
			if !alwaysfit && !neverfit {
				rest[s] += class.demand
			}

		}
	}

	fmt.Println("-----\tcap12\tcap1k\tcap2k\tdemand\tsupply\trest")

	for s, set := range sets {

		restriction := false

		if cap12[s] > 0 && cap2k[s] == 0 && demands[s]-2 >= supplies[s] {
			restriction = true
		} else if cap1k[s] > 0 && cap2k[s] == 0 && 2*(demands[s]-1) >= supplies[s] {
			restriction = true
		} else if cap1k[s] > 0 && cap2k[s] == 1 && demands[s]-2 >= supplies[s] {
			restriction = true
		}

		if restriction {

			for i, b := range set {
				if b {
					fmt.Print(i)
				} else {
					fmt.Print("-")
				}

			}
			fmt.Println("\t", cap12[s], "\t", cap1k[s], "\t", cap2k[s], "\t", demands[s], "\t", supplies[s], "\t", rest[s])
		}

	}
	return
}

func createSubSets(i int, set []bool) (sets [][]bool) {

	if i == option_count {
		sets = make([][]bool, 1)
		sets[0] = set
		return
	}

	pos := make([]bool, len(set))
	neg := make([]bool, len(set))
	copy(pos, set)
	copy(neg, set)

	pos[i] = true
	i++
	sets = createSubSets(i, pos)
	sets = append(sets, createSubSets(i, neg)...)
	return
}


func createCapacityConstraints(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

    // first,position,count

    q := c.window
    u := c.capacity

    for first := 0 ; first < size - q + 1; first++ { 
        
        // first,position,count
        cV1 := AtMostVar{c.cId, first, first, 0}
        cV2 := AtMostVar{c.cId, first, first, 1}
        pV  := PosVar{c.cId, first}

	    if *ca3 {
	    	cn := clause{"ca3", []int{getPosId(pV), -getAtMostId(cV2)}}
	    	clauses = append(clauses, cn)
	    }

	    for i := first; i < first + q - 1; i++ {

	    	cV1.pos = i 
	    	cV2.pos = i + 1
	    	pV.pos = i + 1

	    	for j := 0; j <= u+1; j++ {
	    		cV1.count = j
	    		cV2.count = j
	    		if *ca1 {
	    			c1 := clause{"ca1", []int{-1 * getAtMostId(cV1), getAtMostId(cV2)}}
	    			clauses = append(clauses, c1)
	    		}
	    		if *ca3 {
	    			c3 := clause{"ca3", []int{getPosId(pV), getAtMostId(cV1), -getAtMostId(cV2)}}
	    			clauses = append(clauses, c3)
	    		}
	    	}
	    }

        cV1 = AtMostVar{c.cId, first, first, 0}
	    cV2 = AtMostVar{c.cId, first, first, 1}
	    pV = PosVar{c.cId, first}

	    if *ca4 {
	    	cn := clause{"ca4", []int{-getPosId(pV), getAtMostId(cV2)}}
	    	clauses = append(clauses, cn)
	    }

	    for i := first; i < first + q - 1; i++ {

	    	cV1.pos = i
	    	cV2.pos = i + 1
	    	pV.pos = i + 1

	    	for j := 0; j <= u; j++ {
	    		cV1.count = j
	    		cV2.count = j + 1

	    		if *ca2 {
	    			c2 := clause{"ca2", []int{getAtMostId(cV1), -getAtMostId(cV2)}}
	    			clauses = append(clauses, c2)
	    		}
	    		if *ca4 {
	    			c4 := clause{"ca4", []int{-getPosId(pV), -getAtMostId(cV1), getAtMostId(cV2)}}
	    			clauses = append(clauses, c4)
	    		}
	    	}
	    }

        if *ca5 { //initialize

        cV1 := AtMostVar{c.cId, first, first, 2}
        cV2 := AtMostVar{c.cId, first, first + q - 1, u+1}
        cV3 := AtMostVar{c.cId, first, first , 0}

        clauses = append(clauses,clause{"ca5", []int{-getAtMostId(cV1)}})
        clauses = append(clauses,clause{"ca5", []int{-getAtMostId(cV2)}})
        clauses = append(clauses,clause{"ca5", []int{getAtMostId(cV3)}})

        } 

    }

	return

} 


func createCounter(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	pV := PosVar{c.cId, 0}
	cV2 := CountVar{c.cId, 0, 1}

	if *id3 {
		cn := clause{"id3", []int{getPosId(pV), -getCountId(cV2)}}
		clauses = append(clauses, cn)
	}

	for i := 0; i < size-1; i++ {

		cV1 := CountVar{c.cId, i, -1}
		cV2.pos = i + 1
		pV.pos = i + 1

		for j := c.lower[i]; j <= c.upper[i]; j++ {
			cV1.count = j
			cV2.count = j
			if *id1 {
				c1 := clause{"id1", []int{-1 * getCountId(cV1), getCountId(cV2)}}
				clauses = append(clauses, c1)
			}
			if *id3 {
				c3 := clause{"id3", []int{getPosId(pV), getCountId(cV1), -getCountId(cV2)}}
				clauses = append(clauses, c3)
			}
		}
	}

	pV = PosVar{c.cId, 0}
	cV2 = CountVar{c.cId, 0, 1}

	if *id4 {
		cn := clause{"id4", []int{-getPosId(pV), getCountId(cV2)}}
		clauses = append(clauses, cn)
	}

	for i := 0; i < size-1; i++ {

		cV1 := CountVar{c.cId, i, -1}
		cV2.pos = i + 1
		pV.pos = i + 1

		for j := c.lower[i]; j < c.upper[i]; j++ {
			cV1.count = j
			cV2.count = j + 1
			if *id2 {
				c2 := clause{"id2", []int{getCountId(cV1), -getCountId(cV2)}}
				clauses = append(clauses, c2)
			}
			if *id4 {
				c4 := clause{"id4", []int{-getPosId(pV), -getCountId(cV1), getCountId(cV2)}}
				clauses = append(clauses, c4)
			}
		}
	}

	return
}

func createAtMostSeq5(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	var cV CountVar
	cV.cId = c.cId

	for i := 0; i < size; i++ {
		cV.pos = i

		cV.count = c.lower[i]
		cn := clause{"id5", []int{getCountId(cV)}}
		clauses = append(clauses, cn)

		cV.count = c.upper[i]
		cn = clause{"id5", []int{-getCountId(cV)}}
		clauses = append(clauses, cn)
	}

	return
}

func createAtMostSeq6(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	var cV1, cV2 CountVar

	cV1.cId = c.cId
	cV2.cId = c.cId
	q := c.window
	u := c.capacity

	if *sbd {
		// needed because I tried to avoid the first column, now extra work for sbd
		cV1.pos = q - 1
		cV1.count = u + 1
		cn := clause{"id6", []int{-getCountId(cV1)}}
		clauses = append(clauses, cn)

	}

	for i := q; i < size; i++ {

		cV1.pos = i - q
		cV2.pos = i

		for j := c.lower[i-q]; j < c.upper[i-q]; j++ {
			cV1.count = j
			cV2.count = j + u
			if c.lower[i] <= j+u && j+u < c.upper[i] {
				cn := clause{"id6", []int{getCountId(cV1), -getCountId(cV2)}}
				clauses = append(clauses, cn)
			}
		}
	}

	return
}

func createAtMostSeq7(cId1 CountableId, cId2 CountableId) (clauses []clause) {

	var pV1, pV2 PosVar

	pV1.cId = cId1
	pV2.cId = cId2

	for i := 0; i < size; i++ {
		pV1.pos = i
		pV2.pos = i
		clauses = append(clauses, clause{"id7", []int{-getPosId(pV1), getPosId(pV2)}})
	}

	return
}

func createAtMostSeq8(cId1 CountableId, cId2s []CountableId) (clauses []clause) {

	var pV1 PosVar

	pV1.cId = cId1

	for i := 0; i < size; i++ {
		pV1.pos = i

		c := make([]int, len(cId2s)+1)
		c[0] = -getPosId(pV1)

		for j, id := range cId2s {
			c[j+1] = getPosId(PosVar{id, i})
		}

		clauses = append(clauses, clause{"id8", c})
	}

	return
}

func createAtMostSeq9(cId1 CountableId, cId2 CountableId) (clauses []clause) {

	var pV1, pV2 PosVar

	pV1.cId = cId1
	pV2.cId = cId2

	for i := 0; i < size; i++ {
		pV1.pos = i
		pV2.pos = i
		clauses = append(clauses, clause{"id9", []int{-getPosId(pV1), -getPosId(pV2)}})
	}

	return
}

func createExactlyOne() (clauses []clause) {

	clauses = make([]clause, 0)

	var posV1, posV2, auxV1, auxV2 PosVar

	for i := 0; i < size; i++ {

		posV1.pos = i
		posV2.pos = i
		auxV1.pos = i
		auxV2.pos = i

		atLeastOne := make([]int, class_count)

		for j := 0; j < class_count-1; j++ {

			posV1.cId = CountableId{classType, j}
			posV2.cId = CountableId{classType, j + 1}
			atLeastOne[j] = getPosId(posV1)

			auxV1.cId = CountableId{exactlyOne, j}
			auxV2.cId = CountableId{exactlyOne, j + 1}

			c1 := clause{"lt1", []int{-getPosId(posV1), getPosId(auxV1)}}
			c2 := clause{"lt1", []int{-getPosId(posV2), -getPosId(auxV1)}}
			clauses = append(clauses, c1, c2)
			if j < class_count-2 {
				c3 := clause{"lt1", []int{-getPosId(auxV1), getPosId(auxV2)}}
				clauses = append(clauses, c3)
			}

		}

		atLeastOne[class_count-1] = getPosId(posV2)
		clauses = append(clauses, clause{"gt1", atLeastOne})

	}

	return
}

func createSymmetry() (clauses []clause) {

	var pV1, pVn PosVar

	pV1.pos = 0
	pVn.pos = size - 1

	for i := 0; i < class_count-1; i++ {

		pV1.cId = CountableId{exactlyOne, i}
		pVn.cId = CountableId{exactlyOne, i}

		clauses = append(clauses, clause{"sym", []int{getPosId(pV1), -getPosId(pVn)}})
	}

	pV1.cId = CountableId{classType, class_count - 1}
	pVn.cId = CountableId{classType, class_count - 1}
	pVn2 := PosVar{CountableId{exactlyOne, class_count - 2}, size - 1}

	clauses = append(clauses, clause{"sym", []int{getPosId(pV1), -getPosId(pVn), -getPosId(pVn2)}})

	return
}

func createRedundant1(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	var pV1, pV2 PosVar

	pV1.cId = c.cId
	pV2.cId = c.cId

	q := c.window
	u := c.capacity

	if u == 1 {
		for i := 0; i < size; i++ {

			pV1.pos = i

			for j := i + 1; j < i+q && j < size; j++ {
				pV2.pos = j
				cn := clause{"re1", []int{-getPosId(pV1), -getPosId(pV2)}}
				clauses = append(clauses, cn)
			}
		}
	}

	return
}

func createRedundant2(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	q := c.window
	u := c.capacity

	if u == 2 {

		var pV1, pV2, pV3 PosVar

		pV1.cId = c.cId
		pV2.cId = c.cId
		pV3.cId = c.cId

		for i := 0; i < size; i++ {

			pV1.pos = i

			for j := i + 1; j < i+q && j < size; j++ {

				pV2.pos = j

				for k := j + 1; k < i+q && k < size; k++ {

					pV3.pos = k

					cn := clause{"re2", []int{-getPosId(pV1), -getPosId(pV2), -getPosId(pV3)}}
					clauses = append(clauses, cn)
				}
			}
		}
	}

	return
}

// only create these with options (1. definition of optimization statement)
func createOptPositions(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	var cV1, cV2 CountVar
	var optV PosVar

	cV1.cId = c.cId
	cV2.cId = c.cId
	optV.cId = c.cId
	optV.cId.typ = optimizationType

	q := c.window
	u := c.capacity

	if *sbd {
		// needed because avoid zero column, now extra work for sbd
		cV1.pos = q - 1
		optV.pos = q - 1
		cV1.count = u + 1
		cn := clause{"op1", []int{getPosId(optV), -getCountId(cV1)}}
		clauses = append(clauses, cn)

	}

	for i := q; i < size; i++ {

		cV1.pos = i - q
		optV.pos = i
		cV2.pos = i

		for j := c.lower[i-q]; j < c.upper[i-q]; j++ {
			cV1.count = j
			cV2.count = j + u
			if j+u < c.upper[i] {
				cn := clause{"op0", []int{getPosId(optV), getCountId(cV1), -getCountId(cV2)}}
				clauses = append(clauses, cn)
			}
		}
	}

	return
}

func createOptCounter(c Countable) (clauses []clause) {

	clauses = make([]clause, 0)

	{ // set upper and lower bound for counters 
		c.lower = make([]int, size)
		c.upper = make([]int, size)

		h := c.demand

		for i := 0; i < size; i++ {
			c.lower[i] = 0
			c.upper[i] = h
			if h <= c.demand {
				h++
			}
		}
	}

	pV := PosVar{c.cId, 0}
	cV2 := CountVar{c.cId, 0, 1}

	for i := *opt - 1; i < size-1; i++ {

		cV1 := CountVar{c.cId, i, -1}
		cV2.pos = i + 1
		pV.pos = i + 1

		for j := c.lower[i]; j <= c.upper[i]; j++ {
			cV1.count = j
			cV2.count = j
			c1 := clause{"op1", []int{-getCountId(cV1), getCountId(cV2)}}
			c3 := clause{"op3", []int{getPosId(pV), getCountId(cV1), -getCountId(cV2)}}
			clauses = append(clauses, c1, c3)
		}
	}

	for i := *opt - 1; i < size-1; i++ {

		cV1 := CountVar{c.cId, i, -1}
		cV2.pos = i + 1
		pV.pos = i + 1

		for j := c.lower[i]; j < c.upper[i]; j++ {
			cV1.count = j
			cV2.count = j + 1
			c2 := clause{"op2", []int{getCountId(cV1), -getCountId(cV2)}}
			c4 := clause{"op4", []int{-getPosId(pV), -getCountId(cV1), getCountId(cV2)}}
			clauses = append(clauses, c2, c4)
		}
	}

	return
}

//func createOptDecision(c Countable, bound int) (clauses []clause) {
//
//}

func (c *Countable) createBounds() {
	if *sbd {
		c.createSimpleBounds()
	} else {
		c.createImprovedBounds()
	}
}

func (c *Countable) createSimpleBounds() {

	c.lower = make([]int, size)
	c.upper = make([]int, size)

	h := c.demand

	for i := size - 1; i >= 0; i-- {
		c.lower[i] = h
		if h > 0 {
			h--
		}
	}

	h = 2

	for i := 0; i < size; i++ {
		c.upper[i] = h
		if h <= c.demand {
			h++
		}
	}
}

func (c *Countable) createImprovedBounds() {
	c.lower = make([]int, size)
	c.upper = make([]int, size)

	h := c.demand

	for i := size - 1; i >= 0; i-- {
		q := c.window
		u := c.capacity

		for i >= 0 {

			c.lower[i] = h

			if u > 0 {
				u--
				if h > 0 {
					h--
				}
			}
			q--
			if q <= 0 {
				break
			}
			i--
		}
	}

	h = 1
	q := c.window - 1
	u := c.capacity - 1

	for i := 0; i < size; i++ {

		for i < size {

			c.upper[i] = h + 1

			if u > 0 && h < c.demand {
				u--
				h++
			}
			q--
			if q <= 0 {
				break
			}
			i++
		}

		q = c.window
		u = c.capacity

	}
}
