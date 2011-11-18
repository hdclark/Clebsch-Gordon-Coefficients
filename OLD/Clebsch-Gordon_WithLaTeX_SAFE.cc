//This program computes Clebsch-Gordon coefficients. It exploits the standard recurrence
// relations. All coefficients are taken to be real.
//
//Precisely, the Clebsch-Gordon coefficients (CGC's) look like
//           < j_{1}, j_{2}, m_{1}, m_{2} | j_{1}, j_{2}, j, m >.
//
//See, for instance, Sakurai '94, Section 3.7 - Addition of Angular Momentum (page 203.)
//Written by haley clark in 2011 for Phys 500 - Quantum Mechanics I, Assignment #4.
//License has not yet been chosen. Please contact the author to help choose one.
//
//The coefficients are stored in a map using a CGCcoeff instance as the key value.
// We are looking for the factor in front, which will necessarily (likely) involve
// the addition of square roots of fractions. We neglect the square root until the 
// end, but we then have to account for addition of square roots. To this end, we
// simply stick each such term in the sum into an element of a vector.

#include <iostream>
#include <string>
#include <cmath>
#include <sstream>
#include <map>
#include <cstdlib>  //div_t, exit
#include <vector>
#include <algorithm>

template <class T>
std::string XtoString(T numb){
    std::stringstream ss;
    ss << numb;
    return ss.str();
}

//################################# frac #####################################
//A simple class to describe fractional integers. Nothing fancy, but we have to
// make our own in C++.
class frac { //Is not guaranteed to elegantly handle zeros!
    public:
        int numer, denom;
        //-------------------------------------- Basic stuff.
        frac(){ //Constructor.
            numer = 0; denom = 1;
        }
        frac(int n, int d){  //Constructor.
            numer = n; denom = d;
            simplify();
        }
        float toFloat() const {
            return static_cast<float>(numer)/static_cast<float>(denom);
        }

        std::string toString() const {
            std::string res = XtoString<int>(numer);
            if(denom != 1){
                res += "/";
                res += XtoString<int>(denom);
            }
            return res;
        }

        std::string toLaTeX() const {
            std::string res;
            if(denom != 1){
                res = " \\frac{" + XtoString<int>(numer) + "}{" + XtoString<int>(denom) + "} ";
            }else{
                res = " " + XtoString<int>(numer) + " ";
            }
            return res;
        }
        void simplify(){
            bool WasAnythingSimplified = false;
            if( numer == 0 ){
                denom = 1;
                return;
            }
            if( denom == 0 ){
                std::cout << "Error: zero denominator encountered. Exiting." << std::endl;
                return;
            } 
            div_t n = std::div(numer, denom); //See if it is complete. Does not handle zeros!
            if(n.rem == 0){
                if((numer != n.quot) && (denom != 1)){ //-1/1 would break it otherwise.
                    numer = n.quot;  denom = 1;
                    WasAnythingSimplified = false; //true; //Needed? //(No.)
                }
            }

            //Eliminate sign redundancies.
            if(denom < 0){
                denom *= -1;  numer *= -1;
                WasAnythingSimplified = false; // true;  //Needed? //(No.)
            }

            //Elimination of common factors. 
            for(int i=2; i<std::max(std::abs(numer),std::abs(denom)); ++i){
                div_t N = std::div(numer, i);
                div_t D = std::div(denom, i);
                if( (N.rem == 0) && (D.rem == 0) ){ //Then this is a common factor.
                    numer /= i;   denom /= i;
                    WasAnythingSimplified = true;
                }
            }

            //Now ~recursively call to simplify duplicate common factors, etc..
            if(WasAnythingSimplified == true) simplify();
            return;
        }

        frac abs(){
            frac res(std::abs(numer), std::abs(denom));
            res.simplify();
            return res;
        }

        frac sign(){
            frac res(numer, denom);
            res.simplify();
            return (res/(res.abs()));
        }

        frac cleansquareroot(){
            //Returns a square root *only* when it is rational number.
            // Incredibly bad way to compute this. Easy enough to understand, though.
            // Returns a ZERO if rational root cannot be found! Also outputs ZERO if
            // input is ZERO - so always check!
            if((numer <= 0) || (denom <= 0)) return frac(0,1);
//            if((numer == 1) && (denom == 1)) return frac(1,1);
            for(int i = 0; i<=numer; ++i) for(int j = 0; j<=denom; ++j){
                if((i*i == numer) && (j*j == denom)){
                    return frac(i,j);
                }
            }
            return frac(0,1);
        }

        bool isASquare(){
            frac res = cleansquareroot();
            if(res*res == (*this)) return true;
            return false;
        }

        //-------------------------------------- Overloaded math.
        frac & operator=(const frac &rhs){
            if (this == &rhs) return *this;
            (*this).denom = rhs.denom; (*this).numer = rhs.numer;
            (*this).simplify();
            return *this;
        }

        frac & operator++(){
            (*this).numer += (*this).denom;
            (*this).simplify();
            return *this;
        }

        frac & operator--(){
            (*this).numer -= (*this).denom; 
            (*this).simplify();
            return *this;
        }

        inline bool operator==(const frac &rhs) const {
            //This function is a tricky one. We cannot rely on simplification.
            frac A( (*this).numer, (*this).denom );  A.simplify();
            frac B(     rhs.numer,     rhs.denom );  B.simplify();
            if( (A.numer == B.numer) && (A.denom == B.denom) ){
                //(If only they were all this easy!)
                return true;
            }else{
                //We resort to an unrespectable low here.
                float eps = 1E-9;
                if( std::fabs( A.toFloat() - B.toFloat() ) < eps ){
                    return true;
                }
            }
            //Here we give up and say they are not equal.
            return false;
        }
        bool operator==(const int rhs){
            frac RHS(rhs,1), THS(numer,denom);
            return (THS == RHS);
        }

        inline bool operator<(const frac &rhs) const {
            return ( toFloat() < rhs.toFloat());
        }

        inline bool operator>=(const frac &rhs) const {
            return !( (*this) < rhs);
        }

        inline bool operator>(const frac &rhs) const {
            return ( toFloat() > rhs.toFloat());
        }

        inline bool operator<=(const frac &rhs) const {
            return !( (*this) > rhs);
        }
 
        frac operator+(const frac &rhs){
            frac res( (*this).numer*rhs.denom + rhs.numer*(*this).denom, (*this).denom*rhs.denom );
            res.simplify();
            return res;
        }
        frac operator+(const int rhs){
            frac RHS(rhs,1), THS(numer,denom);
            frac res = (THS + RHS);
            res.simplify();
            return res;
        }

        frac operator-(const frac &rhs){ //Subtraction.
            frac res( (*this).numer*rhs.denom - rhs.numer*(*this).denom, (*this).denom*rhs.denom );
            res.simplify();
            return res;
        }
        frac operator-(const int rhs){
            frac RHS(rhs,1), THS(numer,denom);
            frac res = (THS - RHS);
            res.simplify();
            return res;
        }

        frac operator*(const frac &rhs){
            frac res( (*this).numer*rhs.numer, (*this).denom*rhs.denom );
            res.simplify();
            return res;
        }
        frac operator*(const int rhs){
            frac RHS(rhs,1), THS(numer,denom);
            frac res = (THS * RHS);
            res.simplify();
            return res;
        }

        frac operator/(const frac &rhs){
            frac res( (*this).numer*rhs.denom, (*this).denom*rhs.numer );
            res.simplify();
            return res;
        }
        frac operator/(const int rhs){
            frac RHS(rhs,1), THS(numer,denom);
            frac res = (THS / RHS);
            res.simplify();
            return res;
        }

        //Friend functions.
        friend frac operator-(const frac &unary); //The negative.

};

frac operator-(const frac &unary){ //Friend function: The negative.
    frac res( -unary.numer, unary.denom );
    res.simplify();
    return res;
}

std::ostream & operator<<( std::ostream &out, const frac &L ) {
    out << L.toString();
    return out;
}


//############################# CGCcoeff ###################################
//Not a terribly useful class. It is used as a key value for a mapping. It 
// also holds some convenience routines (like printing, etc.)
class CGCcoeff {
    public:
        frac j1, j2, m1, m2, j, m;

        CGCcoeff(frac J1, frac J2, frac M1, frac M2, frac J, frac M){ //Constructor.
            j1 = J1; j2 = J2; m1 = M1; m2 = M2; j = J; m = M;
        }

        std::string toString() const {
            std::string res = "< ";
            res += j1.toString() + ", " + j2.toString() + ", ";
            res += m1.toString() + ", " + m2.toString() + " | ";
            res += j1.toString() + ", " + j2.toString() + ", ";
            res += j.toString()  + ", " + m.toString()  + " >";
            return res;
        }

        std::string toLaTeX() const {
            std::string res = " \\braket{ ";
            res += j1.toLaTeX() + ", " + j2.toLaTeX() + ", ";
            res += m1.toLaTeX() + ", " + m2.toLaTeX() + " }{ ";
            res += j1.toLaTeX() + ", " + j2.toLaTeX() + ", ";
            res += j.toLaTeX()  + ", " + m.toLaTeX()  + " } ";
            return res;
        }

        //-------------------------------------
        inline bool operator<(const CGCcoeff &rhs) const { //Required for using in a map.
            if( j1 < rhs.j1 ) return true;
            if( j1 > rhs.j1 ) return false;
            if( j2 < rhs.j2 ) return true;
            if( j2 > rhs.j2 ) return false;
            if( m1 < rhs.m1 ) return true;
            if( m1 > rhs.m1 ) return false;
            if( m2 < rhs.m2 ) return true;
            if( m2 > rhs.m2 ) return false;
            if( j  < rhs.j  ) return true;
            if( j  > rhs.j  ) return false;
            return ( m  < rhs.m  );
        }
};

std::ostream & operator<<( std::ostream &out, const CGCcoeff &L ) {
    out << L.toString();
    return out;
}


//-------------------------------  Physics  ----------------------------------------



void ListAllPossibleCGCs(frac j1, frac j2, frac m1, frac m2, frac j, frac m){
    //Lists all CGC's which satisfy the three constraints:
    //  1)   |m_{1}| <= j_{1}
    //  2)   |m_{2}| <= j_{2}
    //  3)   -j <= |m_{1} + m_{2}| <= j
    //Additionally, we verify that the given numbers are consistent.
    //  4)   |j_{1} - j_{2}| <= j <= (j_{1} + j_{2})
    //  5)   m = m_{1} + m_{2}
    //
    //The values of m1 and m2 here do not matter, but they are kept in for consistent function calling.

    if( ((j1 - j2).abs() > j) || ((j1 + j2) < j) ) return;
    //frac ABS = (j1 - j2).abs();
    //frac SUM = (j1 + j2);
    //if( (ABS > j) || (SUM < j) ) return;


    std::cout << "## List of all CGC's which satisfy the bounds on m1, m2." << std::endl;
    std::cout << "##  j1 = " << j1.toString() << "  j2 = " << j2.toString() << "  j = " << j.toString() << "  m = " << m.toString() << std::endl; 

    for(frac n1 = -j1; n1 <= j1; ++n1) for(frac n2 = -j2; n2 <= j2; ++n2){
        if(m == (n1 + n2)){
            CGCcoeff thecoeff(j1, j2, n1, n2, j, m);
            std::cout << thecoeff.toString() << std::endl;
        }
    }
    return;
}


std::map<CGCcoeff,std::vector<frac> > DetermineAllCGCs(frac j1, frac j2, frac j){
    //This is the meat and potatoes of this code. It cycles through all possible
    // coefficients and determines them in terms of a particular one. They are 
    // then normalized and sent out. At this point, one would receive them, pick 
    // out the ones they need, and then discard the rest.
    //
    //They are sent out in the form of a map<CGCcoeff, vector of fractions>.
    // Each term in the vector represents a square root of the number stored. If 
    // the sign of the number is -, then it is understood that this refers to the
    // sign of the square root.
    //
    //For example, if the vector contained:  (1/2, 3/4, -5/6) then this would 
    // mean that it is actually:  sqrt(1/2) + sqrt(3/4) - sqrt(5/6).
    std::map<CGCcoeff,std::vector<frac> > TheCoeffs;

    //Step 1) Determine the maximum m1 value possible.
    frac m1_max = j1.abs();

    //Step 2) Determine the maximal m2 value with m1 at maximum.
    frac m2_max = (j - m1_max);

    //Step 3) Determine the minimum m1 value possible.
    frac m1_min = -j1.abs();

    //Step 4) Determine the minimal m2 value with m1 at minimum.
    frac m2_min = (-j - m1_min);

    //Step 5) Set the value of the (m1_max,m2_max) CGC coefficient
    //  to be 1. No shenanigans here with m (m = m1 + m2.)
    std::vector<frac> arb;
    arb.push_back( frac(1,1) );
    TheCoeffs[CGCcoeff(j1, j2, m1_max, m2_max, j, m1_max+m2_max)] = arb;

////std::cout << "The prefactor for " << CGCcoeff(j1,j2,m1_max,m2_max,j,m1_max+m2_max) << " is " << arb[0] << std::endl;

    //std::cout << "m1_max  is " << m1_max << std::endl; std::cout << "m2_max  is " << m2_max << std::endl;
    //std::cout << "m1_min  is " << m1_min << std::endl; std::cout << "m2_min  is " << m2_min << std::endl;
    
    //Step 6) Starting at (m1_max,m2_max-1), use the J- relation to
    // determine the coefficient (m1_max,m2_max-1) in terms of 
    // (m1_max,m2_max) and a known (or zero) term to the right.
    // If one cannot be determined, indicate so.

////std::cout << "---- Step 6 - J_ equation - yields :" << std::endl;
 
    for(frac m2 = (m2_max-1); m2 >= -j2; --m2){
        std::vector<frac> PreFactorsA;

        //   J- equation: What are A,B,C factors?
        //
        //    m2|   C 
        //      |    o (m1, m2+1)  x            x
        //      |    |
        //      |    |
        //      |    |
        //      |    |
        //      |    |
        //      |    |A             B
        //      |    o-------------o            x
        //      | (m1,m2)       (m1+1,m2)
        //      |    
        //   ---|----------------------------------
        //      |                          m1
        //      |
        frac m = m1_max + m2 + 1; //Comes from the use of J- on the state.
        frac A = (j  + m )*(j  - m  + 1);
        frac B(0,1); // = (j1 - m1_max)*(j1 + m1_max + 1); //Always zero here.
        frac C = (j2 - m2)*(j2 + m2 + 1);

        //std::cout << "sqrt(" << A << ")" << CGCcoeff(j1,j2,m1_max  ,m2  ,j,m-1) << " = ";
        //std::cout << "sqrt(" << B << ")" << CGCcoeff(j1,j2,m1_max+1,m2  ,j,m  ) << " + ";
        //std::cout << "sqrt(" << C << ")" << CGCcoeff(j1,j2,m1_max  ,m2+1,j,m  ) << std::endl;

        if(A == 0){  
            //If A is ever zero, then we have an issue. Report it and then sepuku!
            std::cerr << "Found a troublesome zero in step 6. Tell the human to fix me." << std::endl;
            exit(0);
        }
        
        //Get the prefactors from the point above (the point denoted C.)
        std::vector<frac> PreFactorsC = TheCoeffs[ CGCcoeff(j1,j2,m1_max,m2+1,j,m) ];
        PreFactorsA.push_back( (C/A)*PreFactorsC[0] );  //Only one number to worry about here.
        if(PreFactorsA.size() != 0){
            TheCoeffs[ CGCcoeff(j1,j2,m1_max,m2,j,m-1) ] = PreFactorsA;
        }

////std::cout << "The prefactor for " << CGCcoeff(j1,j2,m1_max,m2,j,m-1) << " is " << PreFactorsA[0] << std::endl;
    }
    
////std::cout << "TheCoeffs.size() = " << TheCoeffs.size() << std::endl;
////std::cout << std::endl;    

    //Step 7) Use the J+ relation to determine (m1_max-1,m2_max) in
    // terms of (m1_max,m2_max) and (m1_max,m2_max-1).
    //Step 8) Perform the previous step but with m1_max decremented. 
    // Continue this until m1_max-i == m1_min.
////std::cout << "---- Step 7 - J+ equation - yields :" << std::endl;
 
    for(frac m1 = (m1_max);      m1 > m1_min; --m1)
    for(frac m2 = (m2_max); (m2).abs() <= j2; --m2)
    if( (-j <= (m1-1+m2).abs()) && ( (m1-1+m2).abs() <= j ) ){
        std::vector<frac> PreFactorsB;

////std::cout << "Currently visiting point m1,m2 = " << m1 << "  " << m2 << std::endl;


        //   J+ equation: What are A,B,C factors?
        //
        //    m2|   B              A
        //      |    o-------------o (m1,m2)    x
        //      |  (m1-1,m2)       |
        //      |                  |
        //      |                  |
        //      |                  |
        //      |                  |
        //      |                C |
        //      |    x             o            x
        //      |              (m1,m2-1)
        //      |    
        //   ---|----------------------------------
        //      |                          m1
        //      |
        frac m = m1 + m2 - 1; //Comes from the use of J+ on the state.
        frac A = (j - m)*(j + m + 1);
        frac B = (j1 + m1)*(j1 - m1 + 1); 
        frac C = (j2 + m2)*(j2 - m2 + 1);

        //std::cout << "sqrt(" << A << ")" << CGCcoeff(j1,j2,m1_max  ,m2  ,j,m-1) << " = ";
        //std::cout << "sqrt(" << B << ")" << CGCcoeff(j1,j2,m1_max+1,m2  ,j,m  ) << " + ";
        //std::cout << "sqrt(" << C << ")" << CGCcoeff(j1,j2,m1_max  ,m2+1,j,m  ) << std::endl;

        if(B == 0){  
            //If B is ever zero, then we have an issue. Report it and then sepuku!
            std::cerr << "Found a troublesome zero in step 7. Tell the human to fix me." << std::endl;
            exit(0);
        }

        //Get the prefactors from the local point (point A) and the one below (point C)
        // so we can determine the prefactor for the point to the left (point B.)
        std::vector<frac> PreFactorsA = TheCoeffs[ CGCcoeff(j1,j2,m1,m2,j,m+1) ];
        std::vector<frac> PreFactorsC;
        if( (m2-1).abs() <= j2 ) PreFactorsC = TheCoeffs[ CGCcoeff(j1,j2,m1,m2-1,j,m) ];

        for(size_t i=0; i<PreFactorsA.size(); ++i){
            PreFactorsB.push_back( (A/B)*PreFactorsA[i] );
        }

        for(size_t i=0; i<PreFactorsC.size(); ++i){
            PreFactorsB.push_back( -(C/B)*PreFactorsC[i] );
        }

        if(PreFactorsB.size() != 0){
            TheCoeffs[ CGCcoeff(j1,j2,m1-1,m2,j,m) ] = PreFactorsB;
        }

////std::cout << "The prefactor for " << CGCcoeff(j1,j2,m1-1,m2,j,m) << " is ";
////for(size_t i=0; i<PreFactorsB.size(); ++i){
////    std::cout << PreFactorsB[i] ;
////    if((i+1)<PreFactorsB.size()) std::cout << " + ";
////}
////std::cout << std::endl;
    }
 
////std::cout << "TheCoeffs.size() = " << TheCoeffs.size() << std::endl;

    // At this point, all coefficients below m2_max are known (up to a normalization factor.) 


    //Step 9) Use the J- relation to determine the prefactors for the points 
    // above (m1_max,m2_max). 
////std::cout << "---- Step 9 - J- equation - yields :" << std::endl;

    for(frac m2 =  (m2_max);   m2 <= j2; ++m2)
    for(frac m1 = (m1_max-1); m1 >= -j1; --m1)
    if( (-j <= (m1+m2+1).abs()) && ( (m1+m2+1).abs() <= j ) \
        && ( (m1+1).abs() <= j1 ) && ( (m2+1).abs() <= j2 ) ){ 

        std::vector<frac> PreFactorsC;

////std::cout << "Currently visiting point m1,m2 = " << m1 << "  " << m2 << std::endl;

        //   J- equation: What are A,B,C factors?
        //
        //    m2|   C 
        //      |    o (m1, m2+1)  x            x
        //      |    |
        //      |    |
        //      |    |
        //      |    |
        //      |    |
        //      |    |A             B
        //      |    o-------------o            x
        //      | (m1,m2)       (m1+1,m2)
        //      |    
        //   ---|----------------------------------
        //      |                          m1
        //      |
        frac m = m1 + m2 + 1; //Comes from the use of J- on the state.
        frac A = ( j + m )*( j -  m + 1);
        //if( (-j > (m1+m2).abs()) || ( (m1+m2).abs() > j ) )  A = A * 0;  //<--unnecessary. See below.
        frac B = (j1 - m1)*(j1 + m1 + 1); 
        frac C = (j2 - m2)*(j2 + m2 + 1);
//        && ( m1.abs()     < j1 ) && ( m2.abs()     < j2 ) \


        //std::cout << "sqrt(" << A << ")" << CGCcoeff(j1,j2,m1_max  ,m2  ,j,m-1) << " = ";
        //std::cout << "sqrt(" << B << ")" << CGCcoeff(j1,j2,m1_max+1,m2  ,j,m  ) << " + ";
        //std::cout << "sqrt(" << C << ")" << CGCcoeff(j1,j2,m1_max  ,m2+1,j,m  ) << std::endl;

        if(C == 0){  
            //If C is ever zero, then we have an issue. Report it and then sepuku!
            std::cerr << "Found a troublesome zero in step 9. Tell the human to fix me." << std::endl;
            exit(0);
        }

        //Get the prefactors from the local point (point A) and the one below (point C)
        // so we can determine the prefactor for the point to the left (point B.)
        std::vector<frac> PreFactorsA;
        if( (-j <= (m1+m2).abs()) && ( (m1+m2).abs() <= j ) ) PreFactorsA = TheCoeffs[ CGCcoeff(j1,j2,m1,m2,j,m-1) ];
        std::vector<frac> PreFactorsB = TheCoeffs[ CGCcoeff(j1,j2,m1+1,m2,j,m) ];

        for(size_t i=0; i<PreFactorsA.size(); ++i){
            PreFactorsC.push_back( (A/C)*PreFactorsA[i] );
        }

        for(size_t i=0; i<PreFactorsB.size(); ++i){
            PreFactorsC.push_back( -(B/C)*PreFactorsB[i] );
        }

        if(PreFactorsC.size() != 0){
            TheCoeffs[ CGCcoeff(j1,j2,m1,m2+1,j,m) ] = PreFactorsC;
        }

////std::cout << "The prefactor for " << CGCcoeff(j1,j2,m1,m2+1,j,m) << " is ";
////for(size_t i=0; i<PreFactorsC.size(); ++i){
////    std::cout << PreFactorsC[i] ;
////    if((i+1)<PreFactorsC.size()) std::cout << " + ";
////}
////std::cout << std::endl;
    }


    //At this point, all coefficients specified by (j1, j2, j) should be known, (relative to 
    // the first.) We thus appeal to the normalization condition to determine the absolute
    // coefficients.
    //
    // We take SUM_{m1, m2} |< j_{1}, j_{2}, m_{1}, m_{2} | j_{1}, j_{2}, j, m >|^{2} = 1. 


/*   BROKEN: Here for reference.

    for(frac m = -j; m <= j; ++m){
        //Remember: valid CGC's satisfy (m1+m2=m)
        frac A(0,1);
        for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
            if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) )
            for(size_t i = 0; i < TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ].size(); ++i){
                //Remember: these factors have an implicit square root - no need to square them!
                // A will *also* have an implied square root.
                A = A + (TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i]).abs();
            }
        }
                
        if(A == 0){
            //If A is ever zero, then we have an issue. Report it and then sepuku!
            std::cerr << "Found a troublesome zero during normalization. Tell the human to fix me." << std::endl;
            exit(0);
        }

        //Now we multiply this factor back.
        for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
            if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) )
            for(size_t i = 0; i < TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ].size(); ++i){
                //Remember: these factors have an implicit square root - no need to square them!
                // A will *also* have an implied square root.
                (TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i]) = (TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i]) / A;
            }
        }
    }

*/

    for(frac m = -j; m <= j; ++m){
        //Remember: valid CGC's satisfy (m1+m2=m)
        std::vector<frac> TOT;
        for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
            if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) )
            for(size_t i = 0; i < TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ].size(); ++i)
            for(size_t k = 0; k < TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ].size(); ++k){

                //Remember: these factors have an implicit term-by-term square root!
                // This will *also* have an implied square root. Gross!
                TOT.push_back( TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i] * TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][k] );
            }
        }
/*                
std::cout << "The square of the normalization factor is: " << std::endl;
for(size_t i = 0; i < TOT.size(); ++i){
    std::cout << " sqrt( " << TOT[i] << " ) ";
    if((i+1) < TOT.size()) std::cout << "+";
}           
std::cout << std::endl << std::endl;
*/

        //Now we have to simplify the square roots in TOT, or deal with a square root of a 
        // square root (sqrt(TOT)), which is gross. Empirically, it seems all terms in TOT can
        // be simplified by directly computing their square root. 
        //
        //Remember also that the SIGN of the elements of TOT are understood to be outside the
        // square root.
        //
        //Proceeding carefully and naively from this point...
        frac sum; //This will hold the such of sqrt(TOT[0]) + sqrt(TOT[1]) + sqrt(TOT[2]) + ...

        for(size_t i = 0; i < TOT.size(); ++i){
            frac TA = TOT[i];
            //Trivial simplifications.
            if( TA.abs() == 1 ){
                sum = sum + TA;
                continue;
            }
            if( (TA.abs()).isASquare() ){   //Should ALWAYS be true.
                sum = sum + TA.sign() * (TA.abs()).cleansquareroot();
                continue;
            }

            std::cerr << "Error encountered during simplification of normalization factor. Tell the human who made me." << std::endl;
            std::cerr << "Error finding a square root for: " << TA << std::endl;
            exit(0);
        }

        //We now jettison TOT. Now go back and adjust the CGC's.
        for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
            if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) )
            for(size_t i = 0; i < TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ].size(); ++i){

                TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i] = TheCoeffs[CGCcoeff(j1,j2,m1,m2,j,m) ][i] / sum;
            }
        }

    }

    //At this point, all factors should be computed and normalized. Simplification leaves something to be desired,
    // but there are too many square roots for me to 'whip something up' which is also robust.



    return TheCoeffs;    
}


frac GetCoeff(frac j1, frac j2, frac m1, frac m2, frac j, frac m, std::map<CGCcoeff,std::vector<frac> > &TheMap){
//std::string GetCoeff(frac j1, frac j2, frac m1, frac m2, frac j, frac m, std::map<CGCcoeff,std::vector<frac> > &TheMap){
    //This function gets individual coefficients. It does so by computing all possible 
    // coefficients, normalizing, etc.. So you may want to consider writing a routine
    // to grab multiple coefficients at once if looking for performance.

//    std::map<CGCcoeff,std::vector<frac> > TheMap = DetermineAllCGCs(j1, j2, j);
    std::vector<frac> Factors = TheMap[ CGCcoeff(j1, j2,m1,m2,j,m) ];
    std::string res;

    if(Factors.size() == 0){
        return frac(0,1);
    }

    //Here we can, again, attempt to simplify the results. These numbers do not appear to 
    // form such pretty square roots as the normalization numbers do. We thus try simple
    // things like detecting if two terms will cancel one another.
    //
    //Remember that each term has an implied square root, and the sign is outside the root.


    bool WasAnythingSimplified = true;
    while( WasAnythingSimplified ){
        WasAnythingSimplified = false;
        for(size_t i=0; i<Factors.size(); ++i) for(size_t j=(i+1); j<Factors.size(); ++j){
            if( (Factors[i] + Factors[j]) == 0 ){
                //Then we remove these from the Factors.
                Factors.erase( Factors.begin() + j ); //j is after i, so remove it first!
                Factors.erase( Factors.begin() + i );
                WasAnythingSimplified = true;
                break;
            }
        }
    }

/*
    res = "+ (";
    for(size_t i=0; i<Factors.size(); ++i){
        if( Factors[i].abs() == 1 ){
            res += " " + Factors[i].toString();
        //If positive (handling silly + sign out front.)
        }else if( (Factors[i].abs() == Factors[i]) && (i == 0) ){
            res += " sqrt(" + Factors[i].toString() + ")";
        //If positive.
        }else if( Factors[i].abs() == Factors[i] ){
            res += " +sqrt(" + Factors[i].toString() + ")";
        //If negative.
        }else{
            res += " -sqrt(" + (Factors[i].abs()).toString() + ")";
        }
    }
*/


//--------------------------------------an wild IDEA appears! haley uses THINK!-------------------------

std::vector<frac> test;
for(size_t i=0; i<Factors.size(); ++i) for(size_t j=0; j<Factors.size(); ++j){
    test.push_back( Factors[i] * Factors[j] );
}

////std::cout << "THE TEST VECTOR IS: ";
////for(size_t i=0; i<test.size(); ++i){
////    std::cout << " + sqrt(" << test[i].toString() << ")";
////}
////std::cout << std::endl;

//It is terrible to compute the sum of roots, but if we do the trick* where we square everything, sum,
// and THEN take the square root, it (empirically) seems to allow us to easily sum the nasty roots.
//  (* trick discovered and used in the normalization process. Thus the code here is nearly identical
//     to that code.)
//
//We have to be very careful about the sign, though. For normalization we could care less, but here it 
// matters. Thus, we compute the sign AFTER we compute the simplified numbers.
        frac sum;
        for(size_t i = 0; i < test.size(); ++i){
            frac TA = test[i];
            //Trivial simplifications.
            if( TA.abs() == 1 ){
                sum = sum + TA;
                continue;
            }
            if( (TA.abs()).isASquare() ){ //Should ALWAYS be true.
                sum = sum + TA.sign() * (TA.abs()).cleansquareroot();
                continue;
            }

            std::cerr << "Error encountered during final simplification of coefficients. Tell the human who made me." << std::endl;
            exit(0);
        }

//Now the sign.
float precise = 0.0;
for(size_t i=0; i<Factors.size(); ++i){
    precise += (Factors[i].sign()).toFloat() * sqrt( (Factors[i].abs()).toFloat() );
}

if(precise < 0.0){
    sum = sum * (-1);
}

/*
    for(size_t i=0; i<Factors.size(); ++i){
        if( Factors[i].abs() == 1 ){
            res += " " + Factors[i].toString();
        //If positive (handling silly + sign out front.)
        }else if( (Factors[i].abs() == Factors[i]) && (i == 0) ){
            res += " sqrt(" + Factors[i].toString() + ")";
        //If positive.
        }else if( Factors[i].abs() == Factors[i] ){
            res += " +sqrt(" + Factors[i].toString() + ")";
        //If negative.
        }else{
            res += " -sqrt(" + (Factors[i].abs()).toString() + ")";
        }
    }
*/

    //res = "sqrt( " + sum.toString() + ")";



//---------------------------------------------------------  ...it's super effective!  ----------------------------------

    return sum;
//    return res;
}

std::string Decompose(frac j1, frac j2, frac j, frac m){
    //This function gives the complete decomposition and CGC's, states and all.
    std::string res;

    std::map<CGCcoeff,std::vector<frac> > TheMap = DetermineAllCGCs(j1, j2, j);

    res = "|j1,j2,j,m> = ";
    res = "|" + j1.toString() + ", " + j2.toString() + ", " + j.toString() + ", " + m.toString() + " > = ";

    for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
        if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) ){
            frac TheCoeff = GetCoeff(j1,j2,m1,m2,j,m, TheMap);
            res += "\n  + ( sqrt( " + TheCoeff.toString() + " ) ) ";
            res += "|" + j1.toString() + ", " + j2.toString() + ", " + m1.toString() + ", " + m2.toString() + " >";
        }
    }
   
    return res + " .";
}


std::string DecomposeIntoLaTeX(frac j1, frac j2, frac j, frac m){
    //This function gives the complete decomposition and CGC's, states and all.
    std::string res;

    std::map<CGCcoeff,std::vector<frac> > TheMap = DetermineAllCGCs(j1, j2, j);

    res = "\\ket{j1,j2,j,m}  =  ";
    res = "\\ket{" + j1.toLaTeX() + ", " + j2.toLaTeX() + ", " + j.toLaTeX() + ", " + m.toLaTeX() + " } = ";

    bool firstdone = false;
    for(frac m1 = -j1; m1 <= j1; ++m1) for(frac m2 = -j2; m2 <= j2; ++m2){
        if( (-j <= (m1+m2).abs()) && ((m1+m2).abs() <= j) && ( (m1+m2) == m) ){
            frac TheCoeff = GetCoeff(j1,j2,m1,m2,j,m, TheMap);

            if( !(TheCoeff.abs() == 1) ){
                if( TheCoeff == TheCoeff.abs() ){
                    if(firstdone == false){
                        res += " \\sqrt{ " + TheCoeff.toLaTeX() + " } ";
                        firstdone = true;
                    }else{
                        res += " + \\sqrt{ " + TheCoeff.toLaTeX() + " } ";
                    }
                }else{
                    res += " - \\sqrt{ " + (TheCoeff.abs()).toLaTeX() + " } ";
                    firstdone = true;
                }
            }else{
                if( TheCoeff == TheCoeff.abs() ){
                    if(firstdone == false){
                        res += " ";
                        firstdone = true;
                    }else{
                        res += " + ";
                    }
                }else{
                    res += " - ";
                    firstdone = true;
                }
            }

            res += "\\ket{" + j1.toLaTeX() + ", " + j2.toLaTeX() + ", " + m1.toLaTeX() + ", " + m2.toLaTeX() + " }";
        }
    }

    return res;
}



int main(){

   std::cout << "##########################################################################" << std::endl;
   std::cout << "##### For the homework problem, j1=1, j2=2, j=1." << std::endl;
   std::cout << "##########################################################################" << std::endl;
   std::map<CGCcoeff,std::vector<frac> > TheMap = DetermineAllCGCs(frac(1,1), frac(2,1), frac(1,1));
   std::cout << "The number of coefficients computed is:  " << TheMap.size() << std::endl;
   std::cout << "They are : " << std::endl;
   for(std::map<CGCcoeff,std::vector<frac> >::iterator it = TheMap.begin(); it != TheMap.end(); ++it){
       std::cout << (it->first) << " = "; for(size_t i=0; i<(it->second).size(); ++i) std::cout << (it->second)[i] << "  ";  std::cout << std::endl;
   } 


   std::cout << "##########################################################################" << std::endl;
   std::cout << "##### For the homework problem, j1=1, j2=2, j=3." << std::endl;
   std::cout << "##########################################################################" << std::endl;
   TheMap = DetermineAllCGCs(frac(1,1), frac(2,1), frac(3,1));
   std::cout << "The number of coefficients computed is:  " << TheMap.size() << std::endl;
   for(std::map<CGCcoeff,std::vector<frac> >::iterator it = TheMap.begin(); it != TheMap.end(); ++it){
       std::cout << (it->first) << " = "; for(size_t i=0; i<(it->second).size(); ++i) std::cout << (it->second)[i] << "  ";  std::cout << std::endl;
   }

   std::cout << "##########################################################################" << std::endl;
   std::cout << "##### For the two spin-1/2 case, j1=1/2, j2=1/2, j=0." << std::endl;
   std::cout << "##########################################################################" << std::endl;
   TheMap = DetermineAllCGCs(frac(1,2), frac(1,2), frac(0,1));
   std::cout << "The number of coefficients computed is:  " << TheMap.size() << std::endl;
   for(std::map<CGCcoeff,std::vector<frac> >::iterator it = TheMap.begin(); it != TheMap.end(); ++it){
       std::cout << (it->first) << " = "; for(size_t i=0; i<(it->second).size(); ++i) std::cout << (it->second)[i] << "  ";  std::cout << std::endl;
   }

   std::cout << "##########################################################################" << std::endl;
   std::cout << "##### For the two spin-1/2 case, j1=1/2, j2=1/2, j=1." << std::endl;
   std::cout << "##########################################################################" << std::endl;
   TheMap = DetermineAllCGCs(frac(1,2), frac(1,2), frac(1,1));
   std::cout << "The number of coefficients computed is:  " << TheMap.size() << std::endl;
   for(std::map<CGCcoeff,std::vector<frac> >::iterator it = TheMap.begin(); it != TheMap.end(); ++it){
       std::cout << (it->first) << " = "; for(size_t i=0; i<(it->second).size(); ++i) std::cout << (it->second)[i] << "  ";  std::cout << std::endl;
   }


/*
   std::cout << "-------------------------------" << std::endl;
   std::cout << " For the two spin-1/2 case, j1=1/2, j2=1/2, j=1." << std::endl;
   DetermineAllCGCs(frac(1,2), frac(1,2), frac(1,1));
*/



/*
    //Testing the frac class. Seems to work OK, but ensure do 
    // zero denominators pop up anywhere.
    frac A(1,2), B(3,4), C(5,6);
    std::cout << "A     is " << A << std::endl;
    std::cout << "B     is " << B << std::endl;
    std::cout << "C     is " << C << std::endl;
    std::cout << std::endl;
    std::cout << "A+B   is " << A+B << std::endl;
    std::cout << "A-B   is " << A-B << std::endl;
    std::cout << "A+C   is " << A+C << std::endl;
    std::cout << "A-C   is " << A-C << std::endl;
    std::cout << "A*B   is " << A*B << std::endl;
    std::cout << std::endl;
    std::cout << "A/B   is " << A/B << std::endl;
    std::cout << "A+B+C is " << A+B+C << std::endl;
    std::cout << "A+C+B is " << A+C+B << std::endl;
    std::cout << "A/C   is " << A/C << std::endl;
    std::cout << "++A   is " << ++A << std::endl;
    std::cout << std::endl;
    frac D(0,1);
    std::cout << "D     is " << D << std::endl;
    std::cout << "D+A   is " << A+D << std::endl;
    std::cout << "A*D   is " << A*D << std::endl;
*/

 
/*
    frac j1(1,1),  j2(2,1),  m1(1,1),  m2(1,1),  j(1,1),  m(-1,1);
    ListAllPossibleCGCs(j1, j2, m1, m2, j, m);
*/

/*
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(1,1), -frac(1,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(1,1),  frac(0,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(1,1),  frac(1,1));


    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(2,1), -frac(2,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(2,1), -frac(1,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(2,1),  frac(0,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(2,1),  frac(1,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(2,1),  frac(2,1));


    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1), -frac(3,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1), -frac(2,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1), -frac(1,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1),  frac(0,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1),  frac(1,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1),  frac(2,1));
    ListAllPossibleCGCs(frac(1,1), frac(2,1), frac(0,1), frac(0,1), frac(3,1),  frac(3,1));
*/

    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;

   
//    std::cout << GetCoeff(frac(1,2), frac(1,2), frac(-1,2), frac(1,2), frac(0,1), frac(0,1)) << std::endl;

    std::cout << DecomposeIntoLaTeX(frac(1,2), frac(1,2), frac(0,1), frac(0,1)) << std::endl;

    std::cout << DecomposeIntoLaTeX(frac(1,2), frac(1,2), frac(1,1), frac( 1,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,2), frac(1,2), frac(1,1), frac( 0,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,2), frac(1,2), frac(1,1), frac(-1,1)) << std::endl;



    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;


    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(1,1), frac(-1,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(1,1), frac( 0,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(1,1), frac( 1,1)) << std::endl;


    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac(-3,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac(-2,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac(-1,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac( 0,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac( 1,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac( 2,1)) << std::endl;
    std::cout << DecomposeIntoLaTeX(frac(1,1), frac(2,1), frac(3,1), frac( 3,1)) << std::endl;

   
    std::cout << " ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ " << std::endl;

    std::cout << DecomposeIntoLaTeX(frac(3,1), frac(3,2), frac(3,2), frac(-1,2)) << std::endl;

    std::cout << DecomposeIntoLaTeX(frac(3,1), frac(3,2), frac(9,2), frac( 5,2)) << std::endl;
/*

    std::cout << Decompose(frac(5,1), frac(3,2), frac(13,2), frac( 3,2)) << std::endl;


    std::cout << Decompose(frac(18,1), frac(15,2), frac(21,2), frac(-1,2)) << std::endl;
    std::cout << Decompose(frac(18,1), frac(15,2), frac(51,2), frac(21,2)) << std::endl;
*/ 

    return 0;
}
