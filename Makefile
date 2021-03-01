# Ankit Shukla, 27.Jan.2020 (Vienna)
# Copyright 2020 Armin Biere, Ankit Shukla

git = git -c user.name="Auto" -c user.email="auto@auto.com"

SRCDIR = $(PWD)/src

PROGRAM = decision_heuristics 

CXXSOURCES = $(SRCDIR)/DecisionHeuristics.cpp
CXXOBJECTS = $(CXXSOURCES:.cpp=.o)
CXXOBJECTS_debug = $(CXXSOURCES:.cpp=_debug.o)
CXX = g++

Standard_options = --std=c++11 -pedantic
Warning_options = -Wall -Werror
Optimisation_options = -Ofast -DNDEBUG
Debug_options = -g

.PHONY: all 

all: decision_heuristics 

decision_heuristics : $(CXXOBJECTS) 
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) $(LDFLAGS) $(CXXOBJECTS) -o $@

DecisionHeuristics.o : DecisionHeuristics.cpp Makefile
	$(CXX) $(Standard_options) $(Warning_options) $(Optimisation_options) $(CPPFLAGS) $(CXXFLAGS) -c $<

clean:
	$(RM) -f $(CXXOBJECTS) $(PROGRAM)
	$(RM) count *.o *~

run:
	./$(PROGRAM)
