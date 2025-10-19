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

COPY --from=build /root/.m2/repository/com/mysql/mysql-connector-j/9.1.0/mysql-connector-j-9.1.0.jar \
  $CATALINA_HOME/lib/

COPY docker/tomcat/ROOT.xml $CATALINA_HOME/conf/Catalina/localhost/ROOT.xml

EXPOSE 8080
CMD ["catalina.sh", "run"]
