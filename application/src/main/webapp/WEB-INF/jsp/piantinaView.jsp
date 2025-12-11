<%@ page language="java" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.application.model.entity.PostoProiezione" %>
<%@ page import="it.unisa.application.model.entity.Proiezione" %>
<%@ page import="java.util.List" %>
<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Seleziona Posto</title>
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.0/dist/css/bootstrap.min.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css" media="screen">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/piantinaView.min.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/print.css" media="print">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/header.jsp"/>

<div class="container mt-5">
    <div class="row">
        <div class="col-md-8 mb-5">
            <h1 class="text-center mb-4">Seleziona un Posto</h1>
            <div class="legend-posti">
                <div class="legend-item">
                    <span class="legend-square legend-disponibile"></span>
                    <span class="legend-label">Disponibile</span>
                </div>
                <div class="legend-item">
                    <span class="legend-square legend-selezionato"></span>
                    <span class="legend-label">Selezionato</span>
                </div>
                <div class="legend-item">
                    <span class="legend-square legend-occupato"></span>
                    <span class="legend-label">Occupato</span>
                </div>
            </div>


            <div class="d-flex justify-content-center mb-4">
                <div class="schermo p-2 text-center">Schermo</div>
            </div>

            <div class="d-flex flex-wrap justify-content-center" id="posti-container">
                <%
                    List<PostoProiezione> posti = (List<PostoProiezione>) request.getAttribute("postiProiezione");
                    if (posti != null && !posti.isEmpty()) {
                        char currentFila = 0;
                        for (PostoProiezione postoProiezione : posti) {
                            char fila = postoProiezione.getPosto().getFila();
                            int numero = postoProiezione.getPosto().getNumero();
                            boolean disponibile = postoProiezione.isStato();

                            if (fila != currentFila) {
                                if (currentFila != 0) {
                %>
            </div>
            <div class="d-flex flex-wrap justify-content-center">
                <%
                                }
                                currentFila = fila;
                %>
                <div class="col-12 text-center fila-label mb-2">Fila <%= fila %></div>
                <%
                            }
                %>
                <div class="posto <%= disponibile ? "posto-disponibile" : "posto-occupato" %> m-1"
                     data-fila="<%= String.valueOf(fila) %>"
                     data-numero="<%= numero %>"
                     id="posto-<%= fila %>-<%= numero %>"><%= numero %></div>
                <%
                        }
                    } else {
                %>
                <div class="col-12 text-center">
                    <p class="text-muted">Nessun posto disponibile per questa proiezione.</p>
                </div>
                <%
                    }
                %>
            </div>
        </div>

        <div class="col-md-4">
            <div class="checkout-section sticky-top" style="top: 20px;">
                <h3 class="text-center">Riepilogo</h3>
                <h4 class="text-center">Totale: €<span id="totalPrice">0</span></h4>
                <div class="mt-4">
                    <button class="btn btn-danger mb-2" onclick="resetSelection()">Annulla Selezione</button>
                    <form id="checkoutForm" action="${pageContext.request.contextPath}/Checkout" method="get">
                        <input type="hidden" name="proiezioneId"
                               value="<%= ((Proiezione) request.getAttribute("proiezione")).getId() %>">
                        <input type="hidden" name="posti" id="selectedPostiInput">
                        <input type="hidden" name="totale" id="totalPriceInput">
                        <button type="submit" class="btn btn-primary">Checkout</button>
                    </form>
                </div>
            </div>
        </div>
    </div>
</div>

<jsp:include page="/WEB-INF/jsp/footer.jsp"/>
<script src="${pageContext.request.contextPath}/static/js/sceltaPosto.js"></script>
</body>
</html>
