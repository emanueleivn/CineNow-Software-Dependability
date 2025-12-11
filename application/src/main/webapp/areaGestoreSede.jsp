<%@ page import="it.unisa.application.model.entity.GestoreSede" %>
<%@ page import="it.unisa.application.model.entity.Sede" %>
<%@ page import="jakarta.servlet.http.HttpSession" %>
<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<!DOCTYPE html>
<html lang="it">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Area Gestore Sede</title>
  <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.0/dist/css/bootstrap.min.css">
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css">
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/print.css" media="print">
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Baloo+Bhai+2&family=Luckiest+Guy&display=swap" rel="stylesheet">
</head>
<body>
<%
  HttpSession session1 = request.getSession(false);
  GestoreSede gestore = (session1 != null) ? (GestoreSede) session1.getAttribute("gestoreSede") : null;
%>

<jsp:include page="/WEB-INF/jsp/headerSede.jsp"/>

<div class="content">
  <h1>Area Gestore Sede</h1>
  <%
    if (gestore != null) {
  %>
  <p>Benvenuto, <%= gestore.getEmail() %>!</p>
  <p>Ruolo: <%= gestore.getRuolo() %></p>
  <%
    if (gestore.getSede() != null) {
  %>
  <p>Sede associata: <%= gestore.getSede().getNome() %></p>
  <%
  } else {
  %>
  <p>Errore: nessuna sede associata.</p>
  <%
    }
  } else {
  %>
  <p>Errore: non risulti autenticato come Gestore di sede.</p>
  <%
    }
  %>
</div>
<div class="container my-5">
  <div class="text-center my-5">
    <picture>
      <source srcset="${pageContext.request.contextPath}/static/images/logo.webp" type="image/webp">
      <img src="${pageContext.request.contextPath}/static/images/logo.png" alt="CineNow Logo" width="300" height="300" loading="lazy">
    </picture>
  </div>
</div>

<footer>
  <jsp:include page="/WEB-INF/jsp/footer.jsp"/>
</footer>
</body>
</html>