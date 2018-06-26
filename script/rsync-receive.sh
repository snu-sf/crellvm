PROOF_BUILD_DIR=.build-proof

rsync -av \
    --include '*/' \
    --include '*.ml' --include '*.mli' \
    --exclude '*' \
    "$PROOF_BUILD_DIR/" './'

