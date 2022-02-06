/********************************************************************************************
:: README :: [gfGen] Package

[v1.0] First version: Feb. 6, 2022  (JINSOO PARK, isink.park@gmail.com)
 - This package constructs addTable [][]int based on GF(2^m) and a given primitive polynomial, priPoly

 - HOW TO USE this package
	(1) inputExponent : decide m of GF(2^m)
	(2) inputPriPoly : decide a primitive polynomial of GF(2^m)
	(3) run gfConstructGaloisField(inputExponent uint, inputPriPoly *gfPoly) method
	(4) then you can obtain (addTable [i][j]int)
	(5) you can print the addTable by usig gfPrintAddTable() method
 - CONSTRAINTS
	(1) Please use appropriate m and primitive polynomial!
	(2) "Type gfPoly map[uint]uint" is used as "gfPoly[degree] = coefficient" of a polynomial
		ex) priPoly := &gfPoly{0: 1, 1: 1, 3: 1}	// 1x^0 + 1x^1 + 1x^3
 - RESULT
	(1) addTable [][]int
		-> it is a (2^m)-1 square 2-D slice
		-> "addTable[i][j] = k" represents as the following
			=> a^i + a^j = a^k over GF(2^m) with primitive polynomial "priPoly", where a is a primitive element
			=> if i == j, then a^i + a^j = 0, and it is represented by addTable[i][j] = -1

[v1.01] Feb. 6. 2022 (JINSOO PARK, isink.park@gmail.com, https://github.com/parksworks/gfGen)
 - Modify accessablility to use this package

[v1.02] Feb. 6. 2022 (JINSOO PARK, isink.park@gmail.com, https://github.com/parksworks/gfGen)
 - Add a method GfGetAddTable(), returns addTable [][]int by value

 [v1.03] Feb. 6. 2022 (JINSOO PARK, isink.park@gmail.com, https://github.com/parksworks/gfGen)
 - Delete GfGetAddTable()
 - Add GfAdditionOfTwoExponents() method

********************************************************************************************/

package gfGen

import (
	"fmt"
	"math"
)

type GfPoly map[uint]uint // Represents polynomial over Galois field (key: degree, value: exponent of primitive element representing the coefficient of the degree(key))
// [v1.0]	This package consider only for binary coefficient, so the values should be 0 or 1
//		 	For the extension to non-binary coefficient, the values have uint type
type GaloisField struct {
	// This struct works only for GF(2^m)
	// How to use this field: put m and priPoly before use the methods in this struct
	m       uint    // GF(2^m)
	priPoly *GfPoly // primitive polynomial

	fieldSize uint    // 2^m
	addTable  [][]int // addition table (addTable[exp1][exp2] = exponent of coefficient) (!!CAUTION : "-1" represents "zero coefficient")
}

func (gf *GaloisField) GfConstructGaloisField(inputExponent uint, inputPriPoly *GfPoly) error {
	var gfErr error
	// Construct Galois Field of GF(2^m) with the given primitive polynomial
	gf.m = inputExponent
	gf.priPoly = inputPriPoly
	gf.fieldSize, gfErr = gf.intPow(2, gf.m)
	gf.addTable = make([][]int, gf.fieldSize-1)
	for ind := range gf.addTable {
		gf.addTable[ind] = make([]int, gf.fieldSize-1)
	}

	if gfErr == nil {
		// construct exponent <-> binary polynomial expression table
		exp2BinPoly := make([]GfPoly, gf.fieldSize-1)
		for exp := range exp2BinPoly {
			exp2BinPoly[exp] = make(GfPoly)
		}
		gf.gfConstructExp2BinPoly(&exp2BinPoly)

		gfErr = gf.gfConstructAddTable(&exp2BinPoly)

		if gfErr != nil {
			return gfErr
		} else {
			return nil
		}
	} else {
		return gfErr
	}

}

// multiply binary coefficient polynomials p1, p2
func (gf *GaloisField) gfBinaryPolyMulti(p1, p2 *GfPoly) *GfPoly {
	returnPoly := make(GfPoly)
	// p1 * p2 with binary coefficients
	for deg1, coef1 := range *p1 {
		for deg2, coef2 := range *p2 {
			returnPoly[deg1+deg2] = (returnPoly[deg1+deg2] + coef1*coef2) % 2 // binary coefficient multplication
		}
	}
	// delete terms which having zero coefficient
	for deg, coef := range returnPoly {
		if coef == 0 {
			delete(returnPoly, deg)
		}
	}
	return &returnPoly
}

// add binary coefficient polynomials p1, p2
func (gf *GaloisField) gfBinaryPolyAdd(p1, p2 *GfPoly) *GfPoly {
	returnPoly := make(GfPoly)
	// p1 + p2 with binary coefficients
	for deg := uint(0); deg <= gf.m; deg++ {
		_, existDegP1 := (*p1)[deg]
		_, existDegP2 := (*p2)[deg]

		if existDegP1 == existDegP2 { // eliminated term
			returnPoly[deg] = 0
		} else { // added term
			returnPoly[deg] = 1
		}
	}
	// delete terms which having zero coefficient
	for deg, coef := range returnPoly {
		if coef == 0 {
			delete(returnPoly, deg)
		}
	}
	return &returnPoly
}

// modulo binary coefficient polynomial p1 % p2
func (gf *GaloisField) gfBinaryPolyMod(p1, p2 *GfPoly) *GfPoly {
	degDiffMultiplier := make(GfPoly) // multiplier to get divisor

	// copy from p1 to returnPoly
	returnPoly := make(GfPoly)
	for deg, coef := range *p1 {
		returnPoly[deg] = coef
	}

	// polynomial division
	maxDegP2 := gf.gfFindMaxDeg(p2)
	for {
		// check is returnPoly the residual
		maxDegReturnPoly := gf.gfFindMaxDeg(&returnPoly)
		if maxDegReturnPoly < maxDegP2 {
			return &returnPoly
		}

		// continue to divide
		degDiff := maxDegReturnPoly - maxDegP2
		for k := range degDiffMultiplier {
			delete(degDiffMultiplier, k)
		} // clear degDiffMultiplier
		degDiffMultiplier[degDiff] = 1                                  // now, degDiffMultiplier has only a single term x^(degDiff)
		tempDivisorPoly := gf.gfBinaryPolyMulti(p2, &degDiffMultiplier) // get multiplied divisor

		// returnPoly - tempDivisorPoly
		tempSubtResult := gf.gfBinaryPolyAdd(&returnPoly, tempDivisorPoly)
		for k := range returnPoly {
			delete(returnPoly, k)
		}
		for k := range *tempSubtResult {
			returnPoly[k] = (*tempSubtResult)[k]
		}
	}
}

// construct exp2BinPoly table
func (gf *GaloisField) gfConstructExp2BinPoly(exp2BinPoly *([]GfPoly)) {
	// trivial cases
	for exp := uint(0); exp < gf.m; exp++ {
		(*exp2BinPoly)[exp][exp] = 1
	}
	// the other cases
	for exp := gf.m; exp < gf.fieldSize-1; exp++ {
		tempPoly := gf.gfBinaryPolyMulti(&(*exp2BinPoly)[exp-1], &(GfPoly{1: 1})) // multiply (x) to polynomial of tje previous exponent
		(*exp2BinPoly)[exp] = *gf.gfBinaryPolyMod(tempPoly, gf.priPoly)
	}
}

// constcut addTable table
func (gf *GaloisField) gfConstructAddTable(exp2BinPoly *([]GfPoly)) error {
	for exp1 := uint(0); exp1 < gf.fieldSize-1; exp1++ {
		for exp2 := uint(0); exp2 < gf.fieldSize-1; exp2++ {
			if exp1 == exp2 {
				gf.addTable[exp1][exp2] = -1 // "zero" coefficient!
			} else {
				resultPoly := gf.gfBinaryPolyAdd(&(*exp2BinPoly)[exp1], &(*exp2BinPoly)[exp2])

				resultExp, err := gf.gfFindExpByPoly(resultPoly, exp2BinPoly)
				if err != nil {
					return err
				} else {
					gf.addTable[exp1][exp2] = int(resultExp)
				}
			}
		}
	}
	return nil
}

// return exp corresponding to the input polynomial
func (gf *GaloisField) gfFindExpByPoly(poly *GfPoly, exp2BinPoly *([]GfPoly)) (uint, error) {
	for exp := uint(0); exp < gf.fieldSize-1; exp++ { // for each polynomial candidate
		flag := true
		for deg := uint(0); deg <= gf.m; deg++ { // is poly the same as the candidate polynomial?
			_, existDegPoly := (*poly)[deg]
			_, existExp2BinPoly := (*exp2BinPoly)[exp][deg]
			if existDegPoly != existExp2BinPoly {
				flag = false
				break
			}
		}
		if flag {
			return exp, nil
		}
	}
	return 0, fmt.Errorf("[galoisField] Cannot find the given polynomial in the exp2BinPoly table!")
}

// return max degree of a given polynomial
func (gf *GaloisField) gfFindMaxDeg(poly *GfPoly) uint {
	maxDeg := uint(0)
	for deg, _ := range *poly {
		if deg > maxDeg {
			maxDeg = deg
		}
	}
	return maxDeg
}

// return base^exp
func (gf GaloisField) intPow(base uint, exp uint) (uint, error) {
	if base == 0 {
		return 0, fmt.Errorf("[galoisField] base of intPow(base uint, exp uint) should not be 0!")
	}

	limitChecker := math.MaxUint / base
	dummyMult := base
	for iter := uint(1); iter < exp; iter++ {
		dummyMult *= base
		if (dummyMult > limitChecker) && (iter < exp-1) {
			return 0, fmt.Errorf("[galoisField] Too big field size! Please input smaller integer than %d to ConstructGaloisField()!", gf.m)
		}
	}
	return dummyMult, nil
}

// print addTable
func (gf *GaloisField) GfPrintAddTable() {
	if gf.addTable[0][0] == 0 { // not yet calculated
		fmt.Println("[galoisField] Please use gfConstructGaloisField() method first!")
	} else {
		fmt.Println("[galoisField] addTable [i][j]int")
		fmt.Printf("i\\j\t|")
		for i := uint(0); i < gf.fieldSize-1; i++ {
			fmt.Printf("%d\t", i)
		}
		fmt.Println("")
		for i := uint(0); i < gf.fieldSize; i++ {
			fmt.Printf("--------")
		}
		fmt.Println("")

		for i := uint(0); i < gf.fieldSize-1; i++ {
			fmt.Printf("%d\t|", i)
			for j := uint(0); j < gf.fieldSize-1; j++ {
				fmt.Printf("%d\t", gf.addTable[i][j])
			}
			fmt.Println("")
		}
	}
}

// return pointer of addTable
func (gf *GaloisField) GfAdditionOfTwoExponents(exp1, exp2 uint) int {
	return gf.addTable[exp1][exp2]
}

/* [Example] See the following example */
/*
func main() {
	var testGf GaloisField
	priPoly := &GfPoly{0: 1, 1: 1, 3: 1} // 1x^0 + 1x^1 + 1x^3

	gfErr := testGf.GfConstructGaloisField(3, priPoly) // GF(2^3) with primitive polynomial (1x^0 + 1x^1 + 1x^3)
	if gfErr != nil {
		fmt.Printf("gfErr: %v\n", gfErr)
	} else {
		testGf.GfPrintAddTable()
	}

	for i := uint(0); i < testGf.fieldSize-1; i++ {
		fmt.Printf("%d\t|", i)
		for j := uint(0); j < testGf.fieldSize-1; j++ {
			fmt.Printf("%d\t", testGf.GfAdditionOfTwoExponents(i, j))
		}
		fmt.Println("")
	}
}
*/
