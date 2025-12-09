<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<%@ page import="java.util.List" %>
<%@ page import="it.unisa.application.model.entity.Proiezione" %>
<!DOCTYPE html>
<html lang="it">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Gestione Programmazione</title>
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.css">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/headerSede.jsp"/>

<div class="container mt-5">
    <h1 class="text-center mb-4">Gestione Programmazione</h1>
    <%
        Integer sedeId = (Integer) request.getAttribute("sedeId");
        if (sedeId == null) {
            sedeId = Integer.parseInt(request.getParameter("sedeId"));
        }
    %>
    <a href="<%= request.getContextPath() %>/aggiungiProiezione?sedeId=<%= sedeId %>"
       class="btn btn-primary mb-4">Aggiungi Proiezione</a>
    <div class="table-responsive">
        <%
            List<Proiezione> programmazioni = (List<Proiezione>) request.getAttribute("programmazioni");
            if (programmazioni != null && !programmazioni.isEmpty()) {
        %>
        <table class="table table-striped table-bordered">
            <thead class="thead-dark">
            <tr>
                <th scope="col">Sala</th>
                <th scope="col">Data</th>
                <th scope="col">Ora Inizio</th>
                <th scope="col">Film</th>
            </tr>
            </thead>
            <tbody>
            <%
                for (Proiezione p : programmazioni) {
            %>
            <tr>
                <td>Sala <%= p.getSalaProiezione().getNumeroSala() %></td>
                <td><%= p.getDataProiezione() %></td>
                <td><%= p.getOrarioProiezione().getOraInizio() %></td>
                <td><%= p.getFilmProiezione().getTitolo() %></td>
            </tr>
            <%
                }
            %>
            </tbody>
        </table>

        <%-- Paginazione --%>
        <%
            Integer currentPage = (Integer) request.getAttribute("currentPage");
            Integer totalPages = (Integer) request.getAttribute("totalPages");
            if (totalPages != null && totalPages > 1) {
        %>
        <div class="pagination-container">
            <% if (currentPage > 1) { %>
            <a href="${pageContext.request.contextPath}/gestioneProgrammazione?sedeId=<%= sedeId %>&page=<%= currentPage - 1 %>" class="btn-pagination">&larr; Precedente</a>
            <% } else { %>
            <span class="btn-pagination disabled">&larr; Precedente</span>
            <% } %>

            <span class="page-info">Pagina <%= currentPage %> di <%= totalPages %></span>

            <% if (currentPage < totalPages) { %>
            <a href="${pageContext.request.contextPath}/gestioneProgrammazione?sedeId=<%= sedeId %>&page=<%= currentPage + 1 %>" class="btn-pagination">Successiva &rarr;</a>
            <% } else { %>
            <span class="btn-pagination disabled">Successiva &rarr;</span>
            <% } %>
        </div>
        <% } %>
        <%
        } else {
        %>
        <div class="alert alert-warning text-center" role="alert">
            Nessuna proiezione presente.
        </div>
        <%
            }
        %>
    </div>
</div>

<jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</body>
</html>
