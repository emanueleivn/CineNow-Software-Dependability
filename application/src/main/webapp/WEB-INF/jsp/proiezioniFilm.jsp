<%@ page language="java" contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.application.model.entity.Proiezione" %>
<%@ page import="java.util.List" %>
<!DOCTYPE html>
<html lang="it">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Proiezioni - <%= request.getAttribute("filmNome") %> - <%= request.getAttribute("sedeNome") %></title>
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.css">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/header.jsp"/>

<div class="container mt-5">
  <h1 class="text-center mb-4">Proiezioni - <%= request.getAttribute("filmNome") %> - <%= request.getAttribute("sedeNome") %></h1>
  <div class="table-responsive">
    <%
      List<Proiezione> proiezioni = (List<Proiezione>) request.getAttribute("programmazioneFilm");
      if (proiezioni != null && !proiezioni.isEmpty()) {
    %>
    <table class="table table-striped table-bordered">
      <thead class="thead-dark">
      <tr>
        <th scope="col">Data</th>
        <th scope="col">Orario</th>
        <th scope="col">Sala</th>
        <th scope="col">Azioni</th>
      </tr>
      </thead>
      <tbody>
      <%
        for (Proiezione proiezione : proiezioni) {
          String data = proiezione.getDataProiezione().toString();
          String orario = proiezione.getOrarioProiezione().getOraInizio().toString();
          int sala = proiezione.getSalaProiezione().getNumeroSala();
      %>
      <tr>
        <td><%= data %></td>
        <td><%= orario %></td>
        <td>Sala <%= sala %></td>
        <td>
          <form action="${pageContext.request.contextPath}/SceltaPosto" method="post" class="d-inline">
            <input type="hidden" name="proiezioneId" value="<%= proiezione.getId() %>">
            <button type="submit" class="btn btn-primary">Seleziona Posto</button>
          </form>
        </td>
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
      Integer filmId = (Integer) request.getAttribute("filmId");
      Integer sedeId = (Integer) request.getAttribute("sedeId");
      if (totalPages != null && totalPages > 1) {
    %>
    <div class="pagination-container">
      <% if (currentPage > 1) { %>
      <a href="${pageContext.request.contextPath}/ProiezioniFilm?filmId=<%= filmId %>&sedeId=<%= sedeId %>&page=<%= currentPage - 1 %>" class="btn-pagination">&larr; Precedente</a>
      <% } else { %>
      <span class="btn-pagination disabled">&larr; Precedente</span>
      <% } %>

      <span class="page-info">Pagina <%= currentPage %> di <%= totalPages %></span>

      <% if (currentPage < totalPages) { %>
      <a href="${pageContext.request.contextPath}/ProiezioniFilm?filmId=<%= filmId %>&sedeId=<%= sedeId %>&page=<%= currentPage + 1 %>" class="btn-pagination">Successiva &rarr;</a>
      <% } else { %>
      <span class="btn-pagination disabled">Successiva &rarr;</span>
      <% } %>
    </div>
    <% } %>
    <%
    } else {
    %>
    <div class="alert alert-warning text-center" role="alert">
      Nessuna proiezione disponibile per questa settimana, torna presto...
    </div>
    <%
      }
    %>
  </div>
</div>

<jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</body>
</html>
