<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.application.model.entity.Film" %>
<%@ page import="it.unisa.application.model.entity.Sala" %>
<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Aggiungi Proiezione</title>
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/aggiungiProiezione.min.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css" media="screen">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/print.css" media="print">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/headerSede.jsp"/>
<script>window.contextPath = "<%= request.getContextPath() %>";</script>

<form action="<%= request.getContextPath() %>/aggiungiProiezione" method="post">
    <input type="hidden" name="sedeId" value="<%= request.getAttribute("sedeId") %>">

    <div>
        <label for="film">Seleziona Film:</label>
        <select id="film" name="film" required>
            <option value="">-- Seleziona --</option>
            <%
                List<Film> films = (List<Film>) request.getAttribute("films");
                if (films != null) {
                    for (Film film : films) {
            %>
            <option value="<%= film.getId() %>"><%= film.getTitolo() %></option>
            <%
                    }
                }
            %>
        </select>
    </div>

    <div>
        <label for="dataInizio">Data Inizio:</label>
        <input type="date" id="dataInizio" name="dataInizio" required>
    </div>

    <div>
        <label for="dataFine">Data Fine:</label>
        <input type="date" id="dataFine" name="dataFine" required>
    </div>

    <div>
        <label for="sala">Seleziona Sala:</label>
        <select id="sala" name="sala" required>
            <option value="">-- Seleziona --</option>
            <%
                List<Sala> sale = (List<Sala>) request.getAttribute("sale");
                if (sale != null) {
                    for (Sala sala : sale) {
            %>
            <option value="<%= sala.getId() %>">Sala <%= sala.getNumeroSala() %></option>
            <%
                    }
                }
            %>
        </select>
    </div>

    <div id="calendar-container">
        <p>Seleziona un film, un intervallo di date e una sala per visualizzare il calendario.</p>
    </div>

    <button type="submit">Aggiungi Proiezione</button>
    <button type="button" onclick="window.location.href='<%= request.getContextPath() %>/gestioneProgrammazione?sedeId=<%= request.getAttribute("sedeId") %>'">Annulla</button>
</form>

<footer>
    <jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</footer>

<script src="https://code.jquery.com/jquery-3.6.0.min.js" defer></script>
<script src="${pageContext.request.contextPath}/static/js/proiezioneCalendar.min.js" defer></script>
</body>
</html>