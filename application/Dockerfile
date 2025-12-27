# ---- Build: produce il WAR ---------------------------------------------------
FROM maven:3.9-eclipse-temurin-21 AS build
WORKDIR /app
COPY pom.xml .
RUN mvn -q -DskipTests dependency:go-offline
COPY src ./src
RUN mvn -q -DskipTests package

# ---- Runtime: Tomcat 11 con JNDI pronto -------------------------------------
FROM tomcat:11.0-jdk21-temurin
ENV CATALINA_HOME=/usr/local/tomcat

COPY --from=build /app/target/*.war $CATALINA_HOME/webapps/ROOT.war

COPY --from=build /root/.m2/repository/com/mysql/mysql-connector-j/9.3.0/mysql-connector-j-9.3.0.jar \
  $CATALINA_HOME/lib/

COPY docker/tomcat/ROOT.xml $CATALINA_HOME/conf/Catalina/localhost/ROOT.xml

# Script di entrypoint per passare le variabili a Tomcat
RUN echo '#!/bin/bash\n\
export CATALINA_OPTS="\
  -DCATALINA_OPTS_DB_HOST=${CATALINA_OPTS_DB_HOST:-db} \
  -DCATALINA_OPTS_DB_PORT=${CATALINA_OPTS_DB_PORT:-3306} \
  -DCATALINA_OPTS_DB_DATABASE=${CATALINA_OPTS_DB_DATABASE:-cinenow} \
  -DCATALINA_OPTS_DB_USER=${CATALINA_OPTS_DB_USER:-cinenow} \
  -DCATALINA_OPTS_DB_PASSWORD=${CATALINA_OPTS_DB_PASSWORD:-cinenow}"\n\
exec catalina.sh run' > /usr/local/bin/entrypoint.sh && chmod +x /usr/local/bin/entrypoint.sh

EXPOSE 8080
ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]

