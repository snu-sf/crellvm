ag -G v$ -s "Admitted" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
echo "---------------------------------------------------------------------------------"
ag -G v$ -s "admit" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
echo "---------------------------------------------------------------------------------"
ag -G v$ -s "SF_ADMIT" --ignore=proof/Adequacy.v --ignore=proof/AdequacyLocal.v --ignore=proof/SimulationNop.v --ignore=status.sh --ignore=count_admit.sh
#-s means case sensitive
#http://minimul.com/ignoring-files-with-ag-silver-searcher.html

#TODO move all proof in "def" to "proof", and only grep "proof".
