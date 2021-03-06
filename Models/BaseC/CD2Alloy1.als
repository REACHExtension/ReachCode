// CD2Alloy1.cd - parsed successfully!
// Alloy Model for CDs CD2Alloy1
// Generated: 2016-07-21 23:49:58 Israel Daylight Time
 
module umlp2alloy/CD2Alloy1_module

///////////////////////////////////////////////////
// Generic Head of CD Model - Apr. 28, 2011
///////////////////////////////////////////////////

//Names of fields/associations in classes of the model
private abstract sig FName {}

//Names of enum values in enums of the model
private abstract sig EnumVal {}

//Values of fields
private abstract sig Val {}

//Parent of all classes relating fields and values
abstract sig Obj {
	get : FName -> { Obj + Val + EnumVal }
}

pred ObjFNames[objs: set Obj, fNames:set  FName] {
	no objs.get[FName - fNames]
}

pred ObjAttrib[objs: set Obj, fName:one FName, fType: set { Obj + Val + EnumVal }] {
	objs.get[fName] in fType
	all o: objs | one o.get[fName]
}

pred ObjMeth[objs: set Obj, fName: one FName, fType: set { Obj + Val + EnumVal }] {
	objs.get[fName] in fType	
	all o: objs | one o.get[fName]
}

pred ObjLUAttrib[objs: set Obj, fName:one FName, fType: set Obj, low: Int, up: Int] {
	ObjLAttrib[objs, fName, fType, low]
	ObjUAttrib[objs, fName, fType, up]
}

pred ObjLAttrib[objs: set Obj, fName:one FName, fType: set Obj, low: Int] {
	objs.get[fName] in fType
	all o: objs | (#o.get[fName] >= low)  
}

pred ObjUAttrib[objs: set Obj, fName:one FName, fType: set Obj, up: Int] {
	objs.get[fName] in fType
	all o: objs | (#o.get[fName] =< up)
}

pred ObjLU[objs: set Obj, fName:one FName, fType: set Obj, low: Int, up: Int] {
	ObjL[objs, fName, fType, low]
	ObjU[objs, fName, fType, up]
}

pred ObjL[objs: set Obj, fName:one FName, fType: set Obj, low: Int] {
	all r: objs | # { l: fType | r in l.get[fName]} >= low
}

pred ObjU[objs: set Obj, fName:one FName, fType: set Obj, up: Int] {
	all r: objs | # { l: fType | r in l.get[fName]} =< up
}

pred BidiAssoc[left: set Obj, lFName:one FName, right: set Obj, rFName:one FName] {
	all l: left | all r: l.get[lFName] | l in r.get[rFName]
	all r: right | all l: r.get[rFName] | r in l.get[lFName]
}

pred Composition[compos: Obj->Obj, right: set Obj] {
	all r: right | lone compos.r
}

fun rel[wholes: set Obj, fn: FName]  : Obj->Obj {
  {o1:Obj,o2:Obj | o1->fn->o2 in wholes <: get}
}

fact NonEmptyInstancesOnly {
  some Obj
}


///////////////////////////////////////////////////
// Structures common to both CDs
///////////////////////////////////////////////////

// Concrete names of fields in cd
private one sig color extends FName {}
private one sig drives extends FName {}
private one sig of extends FName {}
private one sig drivenBy extends FName {}
private one sig worksIn extends FName {}


// Concrete value types in model cd

// Concrete enum values in model cd
private one sig enum_ColorKind_red extends EnumVal {}
private one sig enum_ColorKind_black extends EnumVal {}
private one sig enum_ColorKind_white extends EnumVal {}

// Classes in model cd
sig Employee extends Obj {}
sig Address extends Obj {}
sig Car extends Obj {}
sig Driver extends Obj {}

// Interfaces in model cd

///////////////////////////////////////////////////
// CD CD2Alloy1
///////////////////////////////////////////////////

// Types wrapping subtypes
fun EmployeeSubsCDCD2Alloy1: set Obj  {
    Employee + Driver 
} 
fun AddressSubsCDCD2Alloy1: set Obj  {
    Address 
} 
fun CarSubsCDCD2Alloy1: set Obj  {
    Car 
} 
fun DriverSubsCDCD2Alloy1: set Obj  {
    Driver 
} 

// Types containing subtypes for definition of associations

// Relations that represent compositions which the class is a part of

// Enums
// Enum values in cd
fun ColorKindEnumCDCD2Alloy1: set EnumVal  {
    enum_ColorKind_red + enum_ColorKind_black + enum_ColorKind_white 
} 


// Values and relations in cd
pred CD2Alloy1 {

  // Definition of class Employee
  ObjFNames[Employee,  worksIn +  none]
  // Definition of class Address
  ObjFNames[Address,  none]
  // Definition of class Car
  ObjAttrib[Car, color, ColorKindEnumCDCD2Alloy1]
  ObjFNames[Car,  color +  drivenBy +  none]
  // Definition of class Driver
  ObjFNames[Driver,  drives +  worksIn +  none]
    
  // Special properties of singletons, abstract classes and interfaces

  // Associations
  ObjLUAttrib[EmployeeSubsCDCD2Alloy1, worksIn, AddressSubsCDCD2Alloy1, 1, 3]
  ObjLU[AddressSubsCDCD2Alloy1, worksIn, EmployeeSubsCDCD2Alloy1, 1, 1]
 	BidiAssoc[DriverSubsCDCD2Alloy1, drives, CarSubsCDCD2Alloy1, drivenBy]
  ObjLUAttrib[CarSubsCDCD2Alloy1, drivenBy, DriverSubsCDCD2Alloy1, 1, 1]
  ObjLUAttrib[DriverSubsCDCD2Alloy1, drives, CarSubsCDCD2Alloy1, 0, 1]

	// Compositions

  
  
  Obj = (Employee + Address + Car + Driver)
}


pred cd {
  CD2Alloy1
}


///////////////////////////////////////////////////
// Run commands
///////////////////////////////////////////////////


///////////////////////////////////////////////////
// Run commands
///////////////////////////////////////////////////

run {cd and #FName = 0} for 0 but 5 int
run {cd and #FName < 0 and #EnumVal = 0} for 0 but 5 int
run {cd and #FName < 0 and #EnumVal < 0 and #Val = 0} for 0 but 5 int
run {cd and #FName < 0 and #EnumVal < 0 and #Val < 0 and #Obj = 0} for 0 but 5 int

run {cd and #FName = 1} for 1 but 5 int
run {cd and #FName < 1 and #EnumVal = 1} for 1 but 5 int
run {cd and #FName < 1 and #EnumVal < 1 and #Val = 1} for 1 but 5 int
run {cd and #FName < 1 and #EnumVal < 1 and #Val < 1 and #Obj = 1} for 1 but 5 int

run {cd and #FName = 2} for 2 but 5 int
run {cd and #FName < 2 and #EnumVal = 2} for 2 but 5 int
run {cd and #FName < 2 and #EnumVal < 2 and #Val = 2} for 2 but 5 int
run {cd and #FName < 2 and #EnumVal < 2 and #Val < 2 and #Obj = 2} for 2 but 5 int 

run {cd and #FName = 3} for 3 but 5 int
run {cd and #FName < 3 and #EnumVal = 3} for 3 but 5 int
run {cd and #FName < 3 and #EnumVal < 3 and #Val = 3} for 3 but 5 int
run {cd and #FName < 3 and #EnumVal < 3 and #Val < 3 and #Obj = 3} for 3 but 5 int 

run {cd and #FName = 4} for 4 but 5 int
run {cd and #FName < 4 and #EnumVal = 4} for 4 but 5 int
run {cd and #FName < 4 and #EnumVal < 4 and #Val = 4} for 4 but 5 int
run {cd and #FName < 4 and #EnumVal < 4 and #Val < 4 and #Obj = 4} for 4 but 5 int 

run {cd and #FName = 5} for 5 but 5 int
run {cd and #FName < 5 and #EnumVal = 5} for 5 but 5 int
run {cd and #FName < 5 and #EnumVal < 5 and #Val = 5} for 5 but 5 int
run {cd and #FName < 5 and #EnumVal < 5 and #Val < 5 and #Obj = 5} for 5 but 5 int

run {cd and #FName = 6} for 6 but 5 int
run {cd and #FName < 6 and #EnumVal = 6} for 6 but 5 int
run {cd and #FName < 6 and #EnumVal < 6 and #Val = 6} for 6 but 5 int
run {cd and #FName < 6 and #EnumVal < 6 and #Val < 6 and #Obj = 6} for 6 but 5 int

run {cd and #FName = 7} for 7 but 5 int
run {cd and #FName < 7 and #EnumVal = 7} for 7 but 5 int
run {cd and #FName < 7 and #EnumVal < 7 and #Val = 7} for 7 but 5 int
run {cd and #FName < 7 and #EnumVal < 7 and #Val < 7 and #Obj = 7} for 7 but 5 int 

run {cd and #FName = 8} for 8 but 5 int
run {cd and #FName < 8 and #EnumVal = 8} for 8 but 5 int
run {cd and #FName < 8 and #EnumVal < 8 and #Val = 8} for 8 but 5 int
run {cd and #FName < 8 and #EnumVal < 8 and #Val < 8 and #Obj = 8} for 8 but 5 int

run {cd and #FName = 9} for 9 but 5 int
run {cd and #FName < 9 and #EnumVal = 9} for 9 but 5 int
run {cd and #FName < 9 and #EnumVal < 9 and #Val = 9} for 9 but 5 int
run {cd and #FName < 9 and #EnumVal < 9 and #Val < 9 and #Obj = 9} for 9 but 5 int

run {cd and #FName = 10} for 10 but 5 int
run {cd and #FName < 10 and #EnumVal = 10} for 10 but 5 int
run {cd and #FName < 10 and #EnumVal < 10 and #Val = 10} for 10 but 5 int
run {cd and #FName < 10 and #EnumVal < 10 and #Val < 10 and #Obj = 10} for 10 but 5 int
