echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------Admitted--------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "Admitted" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------admit-----------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "admit" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------SF_ADMIT--------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "SF_ADMIT" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
#-s means case sensitive
#http://minimul.com/ignoring-files-with-ag-silver-searcher.html

#TODO move all proof in "def" to "proof", and only grep "proof".
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------Other assumption keywords---------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
#https://coq.inria.fr/refman/Reference-Manual003.html#Vernacular
#assumption_keyword	::=	Axiom | Conjecture |	Parameter | Parameters |	Variable | Variables |	Hypothesis | Hypotheses
ag -G v$ -s "Axiom" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Conjecture" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Parameter" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Parameters" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Variable" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Variables" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Hypothesis" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Hypotheses" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
