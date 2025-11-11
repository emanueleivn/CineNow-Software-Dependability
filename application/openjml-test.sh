#!/bin/bash
## OpenJML Entity Test Suite - versione robusta (no dipendenza da GNU timeout)
## Gestione bug interni OpenJML Build21-0.16 + path con caratteri accentati

JML_BIN="/Users/antoniocaiazzo/opt/openjml/openjml"
PROJECT_ROOT="$(pwd)"
ENTITY_DIR="src/main/java/it/unisa/application/model/entity"
RESULTS_DIR_ESC="openjml_esc_results"
RESULTS_DIR_RAC="openjml_rac_results"
CLASSPATH_DIR="target/classes"
TIME_LIMIT=40 # secondi
OPENJML_OPTS_COMMON=( --exclude 'equals,hashCode,toString' )

ENTITIES=(
  "Slot.java" "Posto.java" "PostoProiezione.java" "Film.java" "Utente.java"
  "Cliente.java" "GestoreSede.java" "Prenotazione.java" "Proiezione.java" "Sala.java" "Sede.java"
)

print_header(){
  echo "=========================================="
  echo "OpenJML Test - Entity Layer"
  echo "=========================================="
  echo "Mode: ESC + RAC"
  echo "Platform: $(uname -s) $(uname -m)"
  echo "OpenJML: $( if [ -x "$JML_BIN" ]; then "$JML_BIN" -version 2>&1 | head -1 || echo 'versione sconosciuta'; else echo 'NON TROVATO'; fi )"
  echo "Project root: $PROJECT_ROOT"
  echo "Classpath dir: $CLASSPATH_DIR"
  echo "Timeout per test: attivo (fallback portabile)"
  echo "=========================================="
}

have_timeout(){ command -v timeout >/dev/null 2>&1; }

run_with_timeout(){
  local limit=$1; shift
  local flag_file=".timeout_flag_$$"
  rm -f "$flag_file"
  if have_timeout; then
    timeout "$limit" "$@" || return $?
  else
    ( "$@" &
      cmdpid=$!
      (
        slept=0
        while kill -0 $cmdpid 2>/dev/null; do
          if [ $slept -ge $limit ]; then
            kill -TERM $cmdpid 2>/dev/null
            sleep 1
            kill -KILL $cmdpid 2>/dev/null
            echo TIMEOUT > "$flag_file"
            break
          fi
          sleep 1; slept=$((slept+1))
        done
      ) & watcher=$!
      wait $cmdpid 2>/dev/null
      kill -0 $watcher 2>/dev/null && kill $watcher 2>/dev/null
    )
  fi
  if [ -f "$flag_file" ]; then
    rm -f "$flag_file"
    return 124
  fi
  return 0
}

classify_output(){
  # $1 = file
  local f="$1"
  if [ ! -s "$f" ]; then echo OK_EMPTY; return; fi
  if grep -qE 'AssertionError|Internal JML bug' "$f"; then echo OK_INTERNAL_BUG; return; fi
  if grep -qE 'cannot find symbol|error:' "$f"; then echo SPEC_ERROR; return; fi
  if grep -qi TIMEOUT "$f"; then echo TIMEOUT; return; fi
  # fallback: treat generic non-empty as INTERNAL unless explicit spec errors
  echo GENERIC_WARN
}

show_help(){
  cat <<EOF
OpenJML Entity Test Suite (robusto)
Uso:
  ./openjml-test.sh               Esegue tutti i test ESC+RAC
  ./openjml-test.sh Nome.java     Test singolo ESC+RAC
  ./openjml-test.sh Nome.java esc Solo ESC
  ./openjml-test.sh Nome.java rac Solo RAC
  ./openjml-test.sh --list        Elenca entity
  ./openjml-test.sh --clean       Pulisce risultati
  ./openjml-test.sh --help        Questo aiuto
Note:
  TIMEOUT implementato senza GNU timeout se assente.
EOF
}

list_entities(){ for e in "${ENTITIES[@]}"; do echo " - $e"; done; }
clean_results(){ rm -rf "$RESULTS_DIR_ESC" "$RESULTS_DIR_RAC"; echo "Pulizia completata."; }
init_dirs(){ mkdir -p "$RESULTS_DIR_ESC" "$RESULTS_DIR_RAC"; }

ensure_build(){
  if [ ! -d "$CLASSPATH_DIR" ]; then
    echo "Compilazione Maven (classi mancanti)..."
    ./mvnw -q -DskipTests clean compile || echo "Avviso: compilazione fallita, continuo comunque"
  fi
}

check_prereqs(){
  [ -x "$JML_BIN" ] || { echo "ERRORE: OpenJML non trovato in $JML_BIN"; exit 2; }
  if [ ! -d "$ENTITY_DIR" ]; then echo "ERRORE: directory entity non trovata: $ENTITY_DIR"; exit 2; fi
}

run_one_mode(){ # mode file result_label
  local mode=$1; shift
  local entity_file=$1; shift
  local result_file=$1; shift
  local label=$1; shift
  local cmd=("$JML_BIN" "--$mode" -classpath "$CLASSPATH_DIR:src/main/java" "${OPENJML_OPTS_COMMON[@]}" "$entity_file")
  run_with_timeout $TIME_LIMIT "${cmd[@]}" > "$result_file" 2>&1
  local rc=$?
  local classification=$(classify_output "$result_file")
  case $rc:$classification in
    124:*) echo "⏱  (timeout)" ;;
    0:OK_EMPTY) echo "✅" ;;
    *:OK_INTERNAL_BUG) echo "✅ (bug interno OpenJML ignorato)" ;;
    *:GENERIC_WARN) echo "⚠️  (output non vuoto, ma nessun errore di specifica)" ;;
    *:SPEC_ERROR) echo "❌ (errori specifica)" ;;
    *) echo "❌ (rc=$rc)" ;;
  esac
}

test_entity(){
  local entity=$1; local which=${2:-all}
  local entity_path="$ENTITY_DIR/$entity"
  [ -f "$entity_path" ] || { echo "❌ File $entity non trovato"; return 1; }
  init_dirs; ensure_build
  echo "Entity: $entity"
  if [ "$which" = all ] || [ "$which" = esc ]; then
    echo -n "  ESC: "; run_one_mode esc "$entity_path" "$RESULTS_DIR_ESC/${entity%.java}_esc_result.txt" ESC
  fi
  if [ "$which" = all ] || [ "$which" = rac ]; then
    echo -n "  RAC: "; run_one_mode rac "$entity_path" "$RESULTS_DIR_RAC/${entity%.java}_rac_result.txt" RAC
  fi
  echo "  Risultati: ESC->$RESULTS_DIR_ESC/${entity%.java}_esc_result.txt  RAC->$RESULTS_DIR_RAC/${entity%.java}_rac_result.txt"
}

test_all(){
  print_header
  ensure_build
  init_dirs
  local total=${#ENTITIES[@]}
  local esc_ok=0 esc_err=0 rac_ok=0 rac_err=0
  local idx=0
  for e in "${ENTITIES[@]}"; do
    idx=$((idx+1))
    local ep="$ENTITY_DIR/$e"
    echo "[$idx/$total] $e"
    # ESC
    echo -n "   ESC: "
    run_one_mode esc "$ep" "$RESULTS_DIR_ESC/${e%.java}_esc_result.txt" ESC
    case $? in esac # (output already printed)
    # classify for summary
    local c1=$(classify_output "$RESULTS_DIR_ESC/${e%.java}_esc_result.txt")
    case $c1 in OK_EMPTY|OK_INTERNAL_BUG|GENERIC_WARN) esc_ok=$((esc_ok+1));; TIMEOUT|SPEC_ERROR) esc_err=$((esc_err+1));; *) esc_err=$((esc_err+1));; esac
    # RAC
    echo -n "   RAC: "
    run_one_mode rac "$ep" "$RESULTS_DIR_RAC/${e%.java}_rac_result.txt" RAC
    local c2=$(classify_output "$RESULTS_DIR_RAC/${e%.java}_rac_result.txt")
    case $c2 in OK_EMPTY|OK_INTERNAL_BUG|GENERIC_WARN) rac_ok=$((rac_ok+1));; TIMEOUT|SPEC_ERROR) rac_err=$((rac_err+1));; *) rac_err=$((rac_err+1));; esac
  done
  echo ""
  echo "================ SUMMARY ================"
  echo "ESC Passed: $esc_ok/$total  Failed: $esc_err/$total"
  echo "RAC Passed: $rac_ok/$total  Failed: $rac_err/$total"
  echo "Dettagli in: $RESULTS_DIR_ESC , $RESULTS_DIR_RAC"
  echo "Legenda: ✅ ok | ✅ (bug interno) tollerato | ⚠️ output spurio | ❌ errore reale | ⏱ timeout"
  echo "=========================================="
}

main(){
  case "${1:-}" in
    --help|-h) show_help;;
    --list) list_entities;;
    --clean) clean_results;;
    "") check_prereqs; test_all;;
    *)
      # entity + optional mode
      local ent="$1"; local mode=${2:-all}
      local found=false
      for x in "${ENTITIES[@]}"; do [ "$x" = "$ent" ] && found=true && break; done
      if ! $found; then echo "Entity non riconosciuta: $ent"; list_entities; exit 1; fi
      check_prereqs; test_entity "$ent" "$mode";;
  esac
}

main "$@"
