/* sceltaPosto.js - Script per la selezione posti */

// Variabili globali
let selectedSeats = [];
let total = 0;
const seatPrice = 7;

// Funzione di inizializzazione
function initSceltaPosto() {
    const availableSeats = document.querySelectorAll('.posto-disponibile');
    const totalPriceEl = document.getElementById('totalPrice');
    const totalPriceInput = document.getElementById('totalPriceInput');
    const selectedPostiInput = document.getElementById('selectedPostiInput');
    const checkoutButton = document.querySelector('#checkoutForm button[type="submit"]');

    console.log('Posti disponibili trovati:', availableSeats.length);

    // Funzione per aggiornare il riepilogo
    function updateSummary() {
        if (totalPriceEl) {
            totalPriceEl.textContent = total;
        }
        if (totalPriceInput) {
            totalPriceInput.value = total;
        }
        if (selectedPostiInput) {
            selectedPostiInput.value = selectedSeats.join(',');
        }
        console.log('Posti selezionati:', selectedSeats, 'Totale:', total);
    }

    // Funzione per resettare la selezione
    window.resetSelection = function() {
        document.querySelectorAll('.posto-selezionato').forEach(seat => {
            seat.classList.remove('posto-selezionato');
        });
        selectedSeats = [];
        total = 0;
        updateSummary();
    };

    // Aggiungi event listener ai posti disponibili
    availableSeats.forEach(seat => {
        seat.addEventListener('click', function() {
            const fila = seat.dataset.fila;
            const numero = seat.dataset.numero;
            const seatKey = fila + "-" + numero;

            console.log('Click su posto:', seatKey);

            if (seat.classList.contains('posto-selezionato')) {
                // Deseleziona il posto
                seat.classList.remove('posto-selezionato');
                total -= seatPrice;
                selectedSeats = selectedSeats.filter(item => item !== seatKey);
                console.log('Posto deselezionato');
            } else {
                // Seleziona il posto
                seat.classList.add('posto-selezionato');
                total += seatPrice;
                selectedSeats.push(seatKey);
                console.log('Posto selezionato');
            }

            updateSummary();
        });
    });

    // Validazione al momento del checkout
    if (checkoutButton) {
        checkoutButton.addEventListener('click', function(event) {
            if (selectedSeats.length === 0) {
                event.preventDefault();
                alert("Devi selezionare almeno un posto prima di procedere al checkout.");
            }
        });
    }

    // Inizializza il riepilogo
    updateSummary();
}

// Avvia lo script quando il DOM è completamente caricato
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', initSceltaPosto);
} else {
    // Il DOM è già caricato
    initSceltaPosto();
}

