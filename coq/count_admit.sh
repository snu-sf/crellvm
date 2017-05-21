echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------Admitted--------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "Admitted"  --ignore=status.sh --ignore=count_admit.sh
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------admit-----------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "admit"  --ignore=status.sh --ignore=count_admit.sh
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------SF_ADMIT--------------------------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
ag -G v$ -s "SF_ADMIT"  --ignore=status.sh --ignore=count_admit.sh
#-s means case sensitive
#http://minimul.com/ignoring-files-with-ag-silver-searcher.html

#TODO move all proof in "def" to "proof", and only grep "proof".
echo "----------------------------------------------------------------------------------------------------------"
echo "------------------------------Other assumption keywords---------------------------------------------------"
echo "----------------------------------------------------------------------------------------------------------"
#https://coq.inria.fr/refman/Reference-Manual003.html#Vernacular
#assumption_keyword	::=	Axiom | Conjecture |	Parameter | Parameters |	Variable | Variables |	Hypothesis | Hypotheses
ag -G v$ -s "Axiom"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Conjecture"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Parameter"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Parameters"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Variable"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Variables"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Hypothesis"  --ignore=status.sh --ignore=count_admit.sh
ag -G v$ -s "Hypotheses"  --ignore=status.sh --ignore=count_admit.sh
