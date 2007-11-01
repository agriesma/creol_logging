CREOLC = creolc -W all

default:
	$(CREOLC) Interfaces.creol Classes.creol Main.creol


test: Test.maude


%.maude : %.creol
	$(CREOLC) all $<

sense:
	fortune
