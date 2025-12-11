<%@ page import="it.unisa.application.model.entity.Cliente" %>
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>CineNow</title>
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.0/dist/css/bootstrap.min.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/static/style/style.min.css">
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=Baloo+Bhai+2&family=Luckiest+Guy&display=swap" rel="stylesheet">
</head>
<body>
<header>
    <div class="top-bar d-flex align-items-center justify-content-start py-2 px-3">
    </div>

    <nav class="navbar navbar-expand-lg navbar-dark bg-dark" style="background-color: #000000 !important; border: none;">
        <div class="container-fluid">
            <a href="<%= request.getContextPath() %>/areaGestoreCatena.jsp" class="nav-link navbar-brand text-danger fw-bold ms-3">
                <picture>
                    <source srcset="${pageContext.request.contextPath}/static/images/scritta-sito.webp" type="image/webp">
                    <img src="${pageContext.request.contextPath}/static/images/scritta-sito.webp" alt="CineNow" class="ms-3" width="200" height="70" loading="lazy">
                </picture>
            </a>
            <button class="navbar-toggler" type="button" data-bs-toggle="collapse" data-bs-target="#navbarNav"
                    aria-controls="navbarNav" aria-expanded="false" aria-label="Toggle navigation">
                <span class="navbar-toggler-icon"></span>
            </button>
            <div class="collapse navbar-collapse justify-content-center" id="navbarNav">
                <ul class="navbar-nav ms-auto">
                    <li class="nav-item">
                        <a class="nav-link" href="<%= request.getContextPath() %>/areaGestoreCatena.jsp">Home</a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="<%= request.getContextPath() %>/logout">Logout</a>
                    </li>
                    <li class="nav-item">
                        <a class="nav-link" href="<%= request.getContextPath() %>/catalogo">Gestione catalogo</a>
                    </li>
                </ul>
                <span class="navbar-brand text-danger fw-bold ms-auto" style="font-family:'Baloo Bhai 2',sans-serif;">Catena-Movieplex</span>
            </div>
        </div>
    </nav>
</header>
</body>
</html>