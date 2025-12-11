<%@ page contentType="text/html;charset=UTF-8" language="java" %>
<!DOCTYPE html>
<html lang="it">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Area Gestore Catena</title>
  <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.0/dist/css/bootstrap.min.css">
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css">
  <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/print.css" media="print">
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Baloo+Bhai+2&family=Luckiest+Guy&display=swap" rel="stylesheet">
</head>
<body>
<jsp:include page="/WEB-INF/jsp/headerCatena.jsp"/>

<h1 class="text-center my-5">Benvenuto, Gestore della Catena</h1>
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
