<%@ page contentType="text/html;charset=UTF-8" %>

<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CineNow - Checkout</title>
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/print.css" media="print">
    <script src="${pageContext.request.contextPath}/static/js/checkoutValidation.min.js" defer></script>
</head>
<body>

<header>
    <jsp:include page="/WEB-INF/jsp/header.jsp"/>
</header>

<div class="content">
    <div class="form-container">
        <h3>Totale: €<%= request.getParameter("totale") %></h3>
        <h2>Pagamento</h2>
        <div id="error-message" class="error-message" style="display: none;"></div>
        <form id="checkoutForm" action="${pageContext.request.contextPath}/AggiungiOrdine" method="post">
            <input type="text" id="nomeCarta" name="nomeCarta" placeholder="Nome sulla carta" required>
            <input type="text" id="numeroCarta" name="numeroCarta" placeholder="Numero della carta" maxlength="16" required>
            <input type="text" id="scadenzaCarta" name="scadenzaCarta" placeholder="Data di scadenza (MM/AA)" maxlength="5" required>
            <input type="text" id="cvv" name="cvv" placeholder="CVV" maxlength="3" required>
            <input type="hidden" name="proiezioneId" value="<%= request.getParameter("proiezioneId") %>">
            <input type="hidden" name="posti" value="<%= request.getParameter("posti") %>">
            <input type="hidden" name="totale" value="<%= request.getParameter("totale") %>">

            <button type="submit">Conferma</button>
        </form>
    </div>
</div>

<footer>
    <jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</footer>
</body>
</html>
