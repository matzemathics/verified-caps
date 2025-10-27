sudo cpupower frequency-set --governor performance

MODULES=(
    "meta"
    "state::LinkSystem"
    "state::LinkSystem"
    "meta"
    "state::LinkSystem"
    "lemmas::revoke_view"
    "state::LinkSystem"
    "state::LinkSystem"
    "state::LinkSystem"
    "state::LinkSystem"
)

FUNCTIONS=(
    "Meta::revoke_single"
    "State::revoke_put_back_inductive"
    "State::revoke_put_next_inductive"
    "Meta::insert_child"
    "State::insert_child_finish_next_inductive"
    "lemma_revoke_spec"
    "State::finish_insert_inductive"
    "State::finish_revoke_single_inductive"
    "State::revoke_take_back_inductive"
    "State::finish_insert_asserts"
)

mkdir -p results/functions

for I in {1..${#MODULES}}
do
    echo "Verifying ${MODULES[I]}::${FUNCTIONS[I]}"

    cargo verus verify -- \
        --verify-only-module ${MODULES[I]} \
        --verify-function=${FUNCTIONS[I]} \
        --time-expanded \
        --output-json \
    | jq --args '
        .["times-ms"].smt."smt-run-module-times".[]
        | select(.module == $ARGS.positional[0])
        ."function-breakdown".[]
        | select(.function|endswith($ARGS.positional[1]))
        ' ${MODULES[I]} ${FUNCTIONS[I]} \
    | tee -a results/individual-rlmits.json
    # | tee -a results/functions/${MODULES[I]}--${FUNCTIONS[I]}

done

sudo cpupower frequency-set --governor schedutil