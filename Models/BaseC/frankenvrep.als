
abstract sig ArmAngle, Coordinate {}

abstract sig Side{}
lone sig Left extends Side{}
lone sig Right extends Side{}

abstract sig HapticFeedback{}
one sig HapticsEnabled extends HapticFeedback{}
one sig HapticsDisabled extends HapticFeedback{}

abstract sig EffectorType{}
lone sig Cautery_Tissue_Grasper extends EffectorType{}
lone sig Cautery_Shears extends EffectorType{}
lone sig Cautery_Hook extends EffectorType{}
lone sig Tissue_Grasper extends EffectorType{}
lone sig Shears extends EffectorType{}

abstract sig PedalFunction{}
one sig ClutchButton extends PedalFunction{}
one sig HPButton extends PedalFunction{}
one sig ScaleButton extends PedalFunction{}
one sig CauteryButton extends PedalFunction{}

sig PedalButton{
	assigned: one PedalFunction
}

abstract sig Plugin {}

abstract sig GeomagicTouch {
	input: one Coordinate,
	force: some HapticFeedback,
}

abstract one sig RobotApp {
	includes: some Plugin
}

abstract one sig LoadedPlugins {
	loads: some Plugin
}

abstract sig SolverFamily{
	calls: one KinematicModel
}

--specifies the solver
abstract sig KinematicModel{
	solverResult: Coordinate -> ArmAngle
}

abstract one sig Robot {
	arms: some RobotArm
}

abstract sig RobotArm{
	armside: one Side,
	armModel: one ArmType,
	effectorType: one EffectorType
}

abstract sig ArmType {
	anglelimit: set ArmAngle, //set of all the arm angles that are less than limit
	inverseKSolver: one KinematicModel
}

abstract sig RobotControl{
	output: set ArmAngle,
}

one sig Clutch_Plugin extends Plugin{}
one sig GeomagicTouch_plugin extends Plugin{}
one sig HomePosition extends Plugin{}
one sig GrasperLimits extends Plugin{}
one sig Scale extends Plugin{}
one sig DummyController extends Plugin{}
one sig ButtonInterface extends	Plugin{
	setButtonForPedal : some PedalButton
}
abstract sig SolverPlugin extends Plugin{
	solverfamily: one SolverFamily,
}

--return the angles produced from a specific coordinate
fun getArmAngles[s: KinematicModel, c: Coordinate] : one (ArmAngle) {
	s.solverResult[c]
}

--Facts.
--outputs should be in the range of solverResult
fact{
	all o: RobotControl.output | one a: getArmAngles[KinematicModel,Coordinate] | o = a
}

--There is one kinematic model for each robot arm
fact {
    all r: RobotArm | one k: ArmType | r.armModel = k
}

--The solver should be in the armtype solver set
fact {
   KinematicModel in ArmType.*inverseKSolver
}

--all coordinates belong to GMT movements
fact {
	all c: Coordinate | all g : GeomagicTouch | c in g.input
}

--for each of the c coordinates there exists an angle
--and that angle is in the solver result
fact {
	all c: Coordinate | some a: ArmAngle, s : KinematicModel| c->a in s.solverResult
}

--all Plugins belong to RobotApp
fact {
	all p: Plugin | one r: RobotApp | p in r.includes
}

--if the cautery effector is used, scale can't be used
--if the non-cautery tool is used, Grasper limits
--should be added to loads
--and Cautery button shouldn't be assigned
fact{
	(RobotArm.effectorType = Cautery_Tissue_Grasper or
	RobotArm.effectorType = Cautery_Shears or
	RobotArm.effectorType = Cautery_Hook)
	=> ScaleButton not in PedalButton.assigned &&
	CauteryButton in PedalButton.assigned &&
	GrasperLimits not in LoadedPlugins.loads &&
	Scale not in LoadedPlugins.loads
	else
	CauteryButton not in PedalButton.assigned &&
	ScaleButton in PedalButton.assigned &&
	GrasperLimits in LoadedPlugins.loads
}

fact{
	ScaleButton in PedalButton.assigned
	=> Scale in LoadedPlugins.loads
}

fact{
	ClutchButton + HPButton in PedalButton.assigned
}

fact{
	all a, b : PedalButton | a != b implies no a.assigned & b.assigned
}

fact {
	one Robot
	one ArmType
	one GeomagicTouch
	one RobotControl
	one RobotArm
	one SolverPlugin
	one SolverFamily
	some Plugin
}

fact {
	#ArmType.anglelimit > 2 //up to four
	#RobotControl.output > 1
	#PedalButton = 3
	#ButtonInterface.setButtonForPedal = 3
	#Coordinate = 1
}

pred ProduceFeedback[output : RobotControl.output] {
	output not in ArmType.anglelimit
	some notification : GeomagicTouch.force | notification = HapticsEnabled
}


-- solverResult[Coordinate1] is equal to ArmAngle0 unless ArmAngle0 is not in anglelimit


sig armangle extends ArmAngle{}
sig xyz_input extends Coordinate{}

--plugins expected from a typical config file
one sig GeomagicTouchPlugin_instance extends GeomagicTouch_plugin{}
one sig HomePosition_instance extends HomePosition{}
one sig Clutch_instance extends Clutch_Plugin{}
one sig IKSolver_plugin extends SolverPlugin{}
one sig ButtonInterface_instance extends ButtonInterface{}

one sig loaded_plugins_of_ extends LoadedPlugins {}{
	GeomagicTouchPlugin_instance +
	HomePosition_instance +
	Clutch_instance +
	IKSolver_plugin +
	ButtonInterface_instance
	in loads
}

one sig IKSolver_family extends SolverFamily{}{
	calls = FrankenBot
}

one sig FrankenBot extends KinematicModel{}

one sig FrankenVREP extends ArmType{}{
	inverseKSolver = FrankenBot
}

one sig FrankenVREPArm extends RobotArm{}{
	armModel = FrankenVREP
}

one sig UsedGeomagicTouch extends GeomagicTouch {}{
	//force = HapticsDisabled
}

fact {
    HapticsDisabled in	UsedGeomagicTouch.force
}

one sig Current_Robot extends Robot {}{
	arms = FrankenVREPArm
}

fact{
    #ArmType.anglelimit = 4
    #RobotControl.output = 4
	#solverResult = 4
}


pred repair_pred_1 {
all a: RobotControl.output | a not in ArmType.anglelimit
implies ProduceFeedback[a]
}

run {repair_pred_1 and #ArmAngle = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily < 0 and #KinematicModel = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily < 0 and #KinematicModel < 0 and #Robot = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily < 0 and #KinematicModel < 0 and #Robot < 0 and #RobotArm = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily < 0 and #KinematicModel < 0 and #Robot < 0 and #RobotArm < 0 and #ArmType = 0} for 0
run {repair_pred_1 and #ArmAngle < 0 and #Coordinate < 0 and #Side < 0 and #HapticFeedback < 0 and #EffectorType < 0 and #PedalFunction < 0 and #PedalButton < 0 and #Plugin < 0 and #GeomagicTouch < 0 and #RobotApp < 0 and #LoadedPlugins < 0 and #SolverFamily < 0 and #KinematicModel < 0 and #Robot < 0 and #RobotArm < 0 and #ArmType < 0 and #RobotControl = 0} for 0

run {repair_pred_1 and #ArmAngle = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily < 1 and #KinematicModel = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily < 1 and #KinematicModel < 1 and #Robot = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily < 1 and #KinematicModel < 1 and #Robot < 1 and #RobotArm = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily < 1 and #KinematicModel < 1 and #Robot < 1 and #RobotArm < 1 and #ArmType = 1} for 1
run {repair_pred_1 and #ArmAngle < 1 and #Coordinate < 1 and #Side < 1 and #HapticFeedback < 1 and #EffectorType < 1 and #PedalFunction < 1 and #PedalButton < 1 and #Plugin < 1 and #GeomagicTouch < 1 and #RobotApp < 1 and #LoadedPlugins < 1 and #SolverFamily < 1 and #KinematicModel < 1 and #Robot < 1 and #RobotArm < 1 and #ArmType < 1 and #RobotControl = 1} for 1

run {repair_pred_1 and #ArmAngle = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily < 2 and #KinematicModel = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily < 2 and #KinematicModel < 2 and #Robot = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily < 2 and #KinematicModel < 2 and #Robot < 2 and #RobotArm = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily < 2 and #KinematicModel < 2 and #Robot < 2 and #RobotArm < 2 and #ArmType = 2} for 2
run {repair_pred_1 and #ArmAngle < 2 and #Coordinate < 2 and #Side < 2 and #HapticFeedback < 2 and #EffectorType < 2 and #PedalFunction < 2 and #PedalButton < 2 and #Plugin < 2 and #GeomagicTouch < 2 and #RobotApp < 2 and #LoadedPlugins < 2 and #SolverFamily < 2 and #KinematicModel < 2 and #Robot < 2 and #RobotArm < 2 and #ArmType < 2 and #RobotControl = 2} for 2

run {repair_pred_1 and #ArmAngle = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily < 3 and #KinematicModel = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily < 3 and #KinematicModel < 3 and #Robot = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily < 3 and #KinematicModel < 3 and #Robot < 3 and #RobotArm = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily < 3 and #KinematicModel < 3 and #Robot < 3 and #RobotArm < 3 and #ArmType = 3} for 3
run {repair_pred_1 and #ArmAngle < 3 and #Coordinate < 3 and #Side < 3 and #HapticFeedback < 3 and #EffectorType < 3 and #PedalFunction < 3 and #PedalButton < 3 and #Plugin < 3 and #GeomagicTouch < 3 and #RobotApp < 3 and #LoadedPlugins < 3 and #SolverFamily < 3 and #KinematicModel < 3 and #Robot < 3 and #RobotArm < 3 and #ArmType < 3 and #RobotControl = 3} for 3

run {repair_pred_1 and #ArmAngle = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily < 4 and #KinematicModel = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily < 4 and #KinematicModel < 4 and #Robot = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily < 4 and #KinematicModel < 4 and #Robot < 4 and #RobotArm = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily < 4 and #KinematicModel < 4 and #Robot < 4 and #RobotArm < 4 and #ArmType = 4} for 4
run {repair_pred_1 and #ArmAngle < 4 and #Coordinate < 4 and #Side < 4 and #HapticFeedback < 4 and #EffectorType < 4 and #PedalFunction < 4 and #PedalButton < 4 and #Plugin < 4 and #GeomagicTouch < 4 and #RobotApp < 4 and #LoadedPlugins < 4 and #SolverFamily < 4 and #KinematicModel < 4 and #Robot < 4 and #RobotArm < 4 and #ArmType < 4 and #RobotControl = 4} for 4


run {repair_pred_1 and #ArmAngle = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily < 5 and #KinematicModel = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily < 5 and #KinematicModel < 5 and #Robot = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily < 5 and #KinematicModel < 5 and #Robot < 5 and #RobotArm = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily < 5 and #KinematicModel < 5 and #Robot < 5 and #RobotArm < 5 and #ArmType = 5} for 5
run {repair_pred_1 and #ArmAngle < 5 and #Coordinate < 5 and #Side < 5 and #HapticFeedback < 5 and #EffectorType < 5 and #PedalFunction < 5 and #PedalButton < 5 and #Plugin < 5 and #GeomagicTouch < 5 and #RobotApp < 5 and #LoadedPlugins < 5 and #SolverFamily < 5 and #KinematicModel < 5 and #Robot < 5 and #RobotArm < 5 and #ArmType < 5 and #RobotControl = 5} for 5
