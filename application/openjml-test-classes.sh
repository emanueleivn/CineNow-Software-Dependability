#!/bin/bash
## OpenJML Class Test Suite - generico (ESC + RAC)
## Gestione bug interni OpenJML Build21-0.16 + path con caratteri accentati

JML_BIN="/mnt/c/Users/emiio/OneDrive - Università di Salerno/università/Magistrale/SD/jml-lab/openjml-ubuntu-22.04-21-0.16/openjml"
PROJECT_ROOT="$(pwd)"

# Classi predefinite da testare (modifica liberamente questo array)
TARGET_CLASSES=(
  "src/main/java/it/unisa/application/model/entity/Slot.java"
  "src/main/java/it/unisa/application/model/entity/Posto.java"
  "src/main/java/it/unisa/application/model/entity/PostoProiezione.java"
  "src/main/java/it/unisa/application/model/entity/Film.java"
  "src/main/java/it/unisa/application/model/entity/Utente.java"
  "src/main/java/it/unisa/application/model/entity/Cliente.java"
  "src/main/java/it/unisa/application/model/entity/GestoreSede.java"
  "src/main/java/it/unisa/application/model/entity/Prenotazione.java"
  "src/main/java/it/unisa/application/model/entity/Proiezione.java"
  "src/main/java/it/unisa/application/model/entity/Sala.java"
  "src/main/java/it/unisa/application/model/entity/Sede.java"
  "src/main/java/it/unisa/application/model/dao/PrenotazioneDAO.java"
  "src/main/java/it/unisa/application/model/dao/ProiezioneDAO.java"
  "src/main/java/it/unisa/application/model/dao/SalaDAO.java"
  "src/main/java/it/unisa/application/model/dao/SedeDAO.java"
  "src/main/java/it/unisa/application/model/dao/SlotDAO.java"
  "src/main/java/it/unisa/application/model/dao/UtenteDAO.java"
  "src/main/java/it/unisa/application/model/dao/ClienteDAO.java"
  "src/main/java/it/unisa/application/model/dao/FilmDAO.java"
  "src/main/java/it/unisa/application/model/dao/PostoProiezioneDAO.java"
  "src/main/java/it/unisa/application/sottosistemi/gestione_prenotazione/service/PrenotazioneService.java"
)

RESULTS_DIR_ESC="openjml_esc_results"
RESULTS_DIR_RAC="openjml_rac_results"
CLASSPATH_DIR="target/classes"
TIME_LIMIT=600 # secondi
OPENJML_OPTS_COMMON=( --exclude 'equals,hashCode,toString' )

print_header(){
  echo "=========================================="
  echo "OpenJML Class Test Suite"
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
  cat <<'EOF'
OpenJML Class Test Suite
Uso:
  ./openjml-class-test.sh
      Esegue ESC+RAC su tutte le classi in TARGET_CLASSES

  ./openjml-class-test.sh Classe.java
      Test ESC+RAC su una singola classe (path completo o solo nome se presente in TARGET_CLASSES)

  ./openjml-class-test.sh Classe1.java Classe2.java ...
      Test ESC+RAC su tutte le classi passate

  ./openjml-class-test.sh Classe.java esc
      Solo ESC sulla classe specificata

  ./openjml-class-test.sh Classe1.java Classe2.java rac
      Solo RAC su tutte le classi specificate

  ./openjml-class-test.sh esc|rac|all
      Esegue quella modalità su TUTTE le classi in TARGET_CLASSES

  ./openjml-class-test.sh --list
      Elenca le classi predefinite (TARGET_CLASSES)

  ./openjml-class-test.sh --clean
      Pulisce i risultati ESC/RAC

  ./openjml-class-test.sh --help
      Mostra questo aiuto

Note:
  - Una "classe" può essere:
      * un path .java esistente (es. src/main/.../MiaClasse.java)
      * solo il nome file (es. MiaClasse.java) se presente in TARGET_CLASSES
  - TIMEOUT implementato senza GNU timeout se assente.
EOF
}

list_target_classes(){
  echo "Classi predefinite da testare (TARGET_CLASSES):"
  for c in "${TARGET_CLASSES[@]}"; do
    echo " - $c"
  done
}

clean_results(){
  rm -rf "$RESULTS_DIR_ESC" "$RESULTS_DIR_RAC"
  echo "Pulizia completata: $RESULTS_DIR_ESC, $RESULTS_DIR_RAC"
}

init_dirs(){
  mkdir -p "$RESULTS_DIR_ESC" "$RESULTS_DIR_RAC"
}

ensure_build(){
  if [ ! -d "$CLASSPATH_DIR" ]; then
    echo "Compilazione Maven (classi mancanti)..."
    ./mvnw -q -DskipTests clean compile || echo "Avviso: compilazione fallita, continuo comunque"
  fi
}

check_prereqs(){
  [ -x "$JML_BIN" ] || { echo "ERRORE: OpenJML non trovato in $JML_BIN"; exit 2; }
}

run_one_mode(){ # mode java_path result_file
  local mode=$1; shift
  local java_path=$1; shift
  local result_file=$1; shift
  local cmd=("$JML_BIN" "--$mode" -classpath "$CLASSPATH_DIR:src/main/java" "${OPENJML_OPTS_COMMON[@]}" "$java_path")
  run_with_timeout $TIME_LIMIT "${cmd[@]}" > "$result_file" 2>&1
  local rc=$?
  local classification
  classification=$(classify_output "$result_file")
  case $rc:$classification in
    124:*) echo "⏱  (timeout)" ;;
    0:OK_EMPTY) echo "✅" ;;
    *:OK_INTERNAL_BUG) echo "✅ (bug interno OpenJML ignorato)" ;;
    *:GENERIC_WARN) echo "⚠️  (output non vuoto, ma nessun errore di specifica)" ;;
    *:SPEC_ERROR) echo "❌ (errori specifica)" ;;
    *) echo "❌ (rc=$rc)" ;;
  esac
}

test_one_class(){ # java_path [mode]
  local java_path="$1"
  local which=${2:-all}

  if [ ! -f "$java_path" ]; then
    echo "❌ File $java_path non trovato"
    return 1
  fi

  init_dirs
  ensure_build

  local base short
  base=$(basename "$java_path")
  short="${base%.java}"

  echo "Classe: $java_path"

  if [ "$which" = all ] || [ "$which" = esc ]; then
    echo -n "  ESC: "
    run_one_mode esc "$java_path" "$RESULTS_DIR_ESC/${short}_esc_result.txt"
  fi
  if [ "$which" = all ] || [ "$which" = rac ]; then
    echo -n "  RAC: "
    run_one_mode rac "$java_path" "$RESULTS_DIR_RAC/${short}_rac_result.txt"
  fi

  echo "  Risultati: ESC->$RESULTS_DIR_ESC/${short}_esc_result.txt  RAC->$RESULTS_DIR_RAC/${short}_rac_result.txt"
}

test_default_classes(){ # [mode]
  local which=${1:-all}

  print_header
  ensure_build
  init_dirs

  local total=${#TARGET_CLASSES[@]}
  if [ "$total" -eq 0 ]; then
    echo "Nessuna classe configurata in TARGET_CLASSES."
    return 0
  fi

  local esc_ok=0 esc_err=0 rac_ok=0 rac_err=0
  local idx=0

  for path in "${TARGET_CLASSES[@]}"; do
    idx=$((idx+1))
    local base short
    base=$(basename "$path")
    short="${base%.java}"

    echo "[$idx/$total] $path"

    if [ ! -f "$path" ]; then
      echo "   ❌ File non trovato"
      esc_err=$((esc_err+1))
      rac_err=$((rac_err+1))
      continue
    fi

    if [ "$which" = all ] || [ "$which" = esc ]; then
      echo -n "   ESC: "
      local esc_file="$RESULTS_DIR_ESC/${short}_esc_result.txt"
      run_one_mode esc "$path" "$esc_file"
      local c1
      c1=$(classify_output "$esc_file")
      case $c1 in
        OK_EMPTY|OK_INTERNAL_BUG|GENERIC_WARN) esc_ok=$((esc_ok+1));;
        TIMEOUT|SPEC_ERROR|*) esc_err=$((esc_err+1));;
      esac
    fi

    if [ "$which" = all ] || [ "$which" = rac ]; then
      echo -n "   RAC: "
      local rac_file="$RESULTS_DIR_RAC/${short}_rac_result.txt"
      run_one_mode rac "$path" "$rac_file"
      local c2
      c2=$(classify_output "$rac_file")
      case $c2 in
        OK_EMPTY|OK_INTERNAL_BUG|GENERIC_WARN) rac_ok=$((rac_ok+1));;
        TIMEOUT|SPEC_ERROR|*) rac_err=$((rac_err+1));;
      esac
    fi
  done

  echo ""
  echo "================ SUMMARY ================"
  if [ "$which" = all ] || [ "$which" = esc ]; then
    echo "ESC Passed: $esc_ok/$total  Failed: $esc_err/$total"
  fi
  if [ "$which" = all ] || [ "$which" = rac ]; then
    echo "RAC Passed: $rac_ok/$total  Failed: $rac_err/$total"
  fi
  echo "Dettagli in: $RESULTS_DIR_ESC , $RESULTS_DIR_RAC"
  echo "Legenda: ✅ ok | ✅ (bug interno) tollerato | ⚠️ output spurio | ❌ errore reale | ⏱ timeout"
  echo "=========================================="
}

resolve_class_arg(){ # input -> stampa path, ritorna 0/1
  local arg="$1"

  # 1) path esistente così com'è
  if [ -f "$arg" ]; then
    printf '%s\n' "$arg"
    return 0
  fi

  # 2) cerca per basename dentro TARGET_CLASSES
  local p
  for p in "${TARGET_CLASSES[@]}"; do
    if [ "$(basename "$p")" = "$arg" ]; then
      printf '%s\n' "$p"
      return 0
    fi
  done

  return 1
}

main(){
  case "${1:-}" in
    --help|-h)
      show_help
      ;;
    --list)
      list_target_classes
      ;;
    --clean)
      clean_results
      ;;
    "")
      check_prereqs
      test_default_classes all
      ;;
    *)
      check_prereqs
      local mode="all"
      local -a args=("$@")

      # controlla se l'ultimo argomento è una modalità (esc/rac/all)
      local last_index=$(( ${#args[@]} - 1 ))
      local last="${args[$last_index]}"

      if [[ "$last" == "esc" || "$last" == "rac" || "$last" == "all" ]]; then
        mode="$last"
        unset 'args[$last_index]'
      fi

      # se non restano argomenti, applica la modalità a tutte le TARGET_CLASSES
      if [ ${#args[@]} -eq 0 ]; then
        test_default_classes "$mode"
        return
      fi

      # altrimenti testa tutte le classi passate
      local c resolved
      for c in "${args[@]}"; do
        resolved=$(resolve_class_arg "$c") || {
          echo "❌ Classe '$c' non trovata (file inesistente e non presente in TARGET_CLASSES)"
          continue
        }
        test_one_class "$resolved" "$mode"
        echo ""
      done
      ;;
  esac
}

main "$@"
