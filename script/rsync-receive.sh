PROOF_BUILD_DIR=.proof_build

rsync -av \
    --include '*/' \
    --include '*.ml' --include '*.mli' \
    --exclude '*' \
    "$PROOF_BUILD_DIR/" './'

