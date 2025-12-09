<%@ page import="java.util.List" %>
<%@ page import="it.unisa.application.model.entity.Film" %>
<%@ page import="java.util.Base64" %>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<!DOCTYPE html>
<html lang="it">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Gestione Catalogo Film</title>
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.css">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/headerCatena.jsp"/>

<div class="container mt-5">
  <h1 class="text-center mb-4">Gestione Catalogo Film</h1>
  <button class="btn btn-primary mb-4"
          onclick="location.href='<%= request.getContextPath() %>/addFilm'">
    Aggiungi Film
  </button>
  <div class="table-responsive">
    <table class="table table-striped table-bordered">
      <thead class="thead-dark">
      <tr>
        <th scope="col">Titolo</th>
        <th scope="col">Durata</th>
        <th scope="col">Descrizione</th>
        <th scope="col">Classificazione</th>
        <th scope="col">Genere</th>
        <th scope="col">Locandina</th>
      </tr>
      </thead>
      <tbody>
      <%
        List<Film> catalogo = (List<Film>) request.getAttribute("catalogo");
        if (catalogo != null && !catalogo.isEmpty()) {
          for (Film film : catalogo) {
            String base64Image = null;
            if (film.getLocandina() != null && film.getLocandina().length > 0) {
              base64Image = Base64.getEncoder().encodeToString(film.getLocandina());
            }
      %>
      <tr>
        <td><%= film.getTitolo() %></td>
        <td><%= film.getDurata() %> min</td>
        <td><%= film.getDescrizione() %></td>
        <td><%= film.getClassificazione() %></td>
        <td><%= film.getGenere() %></td>
        <td>
          <% if (base64Image != null) { %>
          <img src="data:image/jpeg;base64,<%= base64Image %>"
               alt="Locandina di <%= film.getTitolo() %>"
               width="100" class="img-thumbnail" loading="lazy">
          <% } else { %>
          <span class="text-muted">Nessuna locandina disponibile</span>
          <% } %>
        </td>
      </tr>
      <%
        }
      } else {
      %>
      <tr>
        <td colspan="6" class="text-center">Nessun film disponibile.</td>
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
      <a href="${pageContext.request.contextPath}/catalogo?page=<%= currentPage - 1 %>" class="btn-pagination">&larr; Precedente</a>
      <% } else { %>
      <span class="btn-pagination disabled">&larr; Precedente</span>
      <% } %>

      <span class="page-info">Pagina <%= currentPage %> di <%= totalPages %></span>

      <% if (currentPage < totalPages) { %>
      <a href="${pageContext.request.contextPath}/catalogo?page=<%= currentPage + 1 %>" class="btn-pagination">Successiva &rarr;</a>
      <% } else { %>
      <span class="btn-pagination disabled">Successiva &rarr;</span>
      <% } %>
    </div>
    <% } %>
  </div>
</div>

<jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</body>
</html>
