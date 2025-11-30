import os
import glob
import pandas as pd

# Cartella corrente
FOLDER = "."

# Prende tutti i file guest-navigation_runXX.csv
pattern = os.path.join(FOLDER, "guest-navigation_run*.csv")
files = sorted(glob.glob(pattern))

if not files:
    print(f"Nessun file trovato con pattern: {pattern}")
    raise SystemExit(1)

rows = []

for path in files:
    df = pd.read_csv(path)

    # Colonne importanti
    delta_ms = df["Delta"]                       # millisecondi
    power_w = df["SYSTEM_POWER (Watts)"]         # Watt

    # Durata totale in secondi
    duration_sec = delta_ms.sum() / 1000.0

    # Energia totale in Joule: somma di P * (Delta/1000)
    energy_j = (power_w * (delta_ms / 1000.0)).sum()

    # Potenza media = energia / tempo
    mean_power_w = energy_j / duration_sec if duration_sec > 0 else 0.0

    run_name = os.path.basename(path).replace(".csv", "")

    rows.append({
        "run": run_name,
        "duration_sec": duration_sec,
        "energy_j": energy_j,
        "mean_power_w": mean_power_w,
    })

# DataFrame riassuntivo con una riga per run
summary = pd.DataFrame(rows)

print("Per-run summary:")
print(summary)

# ========= STATISTICHE GLOBALI =========

# Durata
mean_duration = summary["duration_sec"].mean()
var_duration = summary["duration_sec"].var(ddof=1)  # varianza campionaria
std_duration = summary["duration_sec"].std(ddof=1)

# Energia
mean_energy = summary["energy_j"].mean()
var_energy = summary["energy_j"].var(ddof=1)
std_energy = summary["energy_j"].std(ddof=1)

# Potenza media
mean_power = summary["mean_power_w"].mean()
var_power = summary["mean_power_w"].var(ddof=1)
std_power = summary["mean_power_w"].std(ddof=1)

print("\nStatistiche durata (s):")
print(f"Media (T̄)        = {mean_duration:.2f} s")
print(f"Deviazione std σ = {std_duration:.2f} s")
print(f"Varianza s²      = {var_duration:.2f} s^2")

print("\nStatistiche energia (J):")
print(f"Media (Ē)        = {mean_energy:.2f} J")
print(f"Deviazione std σ = {std_energy:.2f} J")
print(f"Varianza s²      = {var_energy:.2f} J^2")

print("\nStatistiche potenza media (W):")
print(f"Media (P̄)        = {mean_power:.2f} W")
print(f"Deviazione std σ = {std_power:.2f} W")
print(f"Varianza s²      = {var_power:.2f} W^2")


# ========= AGGIUNGI MEDIA, VARIANZA E DEVIAZIONE STANDARD AL CSV =========

stats_rows = [
    {
        "run": "MEAN",
        "duration_sec": mean_duration,
        "energy_j": mean_energy,
        "mean_power_w": mean_power,
    },
    {
        "run": "VARIANCE",
        "duration_sec": var_duration,
        "energy_j": var_energy,
        "mean_power_w": var_power,
    },
    {
        "run": "STDDEV",
        "duration_sec": std_duration,
        "energy_j": std_energy,
        "mean_power_w": std_power,
    },
]

summary_with_stats = pd.concat(
    [summary, pd.DataFrame(stats_rows)],
    ignore_index=True
)

out_path = os.path.join(FOLDER, "guest-navigation_before_summary.csv")
summary_with_stats.to_csv(out_path, index=False)
print(f"\nFile riassuntivo (con media e varianza) salvato in: {out_path}")
