-- ==========================================
-- SCHEMA COMPLETO COMPATIBILE CON H2 (MODE=MySQL)
-- ==========================================

CREATE TABLE utente (
                        email VARCHAR(255) PRIMARY KEY,
                        password VARCHAR(255) NOT NULL,
                        ruolo VARCHAR(50) NOT NULL
);

CREATE TABLE cliente (
                         email VARCHAR(255),
                         nome VARCHAR(255) NOT NULL,
                         cognome VARCHAR(255) NOT NULL,
                         PRIMARY KEY (email),
                         FOREIGN KEY (email) REFERENCES utente(email)
                             ON DELETE CASCADE
                             ON UPDATE CASCADE
);

CREATE TABLE sede (
                      id INT AUTO_INCREMENT PRIMARY KEY,
                      nome VARCHAR(255) NOT NULL,
                      via VARCHAR(255) NOT NULL,
                      citta VARCHAR(255) NOT NULL,
                      cap CHAR(5) NOT NULL
);

CREATE TABLE gest_sede (
                           email VARCHAR(255),
                           id_sede INT,
                           PRIMARY KEY (email, id_sede),
                           FOREIGN KEY (email) REFERENCES utente(email)
                               ON DELETE CASCADE
                               ON UPDATE CASCADE,
                           FOREIGN KEY (id_sede) REFERENCES sede(id)
                               ON DELETE CASCADE
                               ON UPDATE CASCADE
);

CREATE TABLE sala (
                      id INT AUTO_INCREMENT PRIMARY KEY,
                      id_sede INT,
                      numero INT NOT NULL,
                      capienza INT NOT NULL,
                      FOREIGN KEY (id_sede) REFERENCES sede(id)
                          ON DELETE CASCADE
                          ON UPDATE CASCADE
);

CREATE TABLE posto (
                       id_sala INT,
                       fila CHAR(1),
                       numero INT,
                       PRIMARY KEY (id_sala, fila, numero),
                       FOREIGN KEY (id_sala) REFERENCES sala(id)
                           ON DELETE CASCADE
                           ON UPDATE CASCADE
);

CREATE TABLE film (
                      id INT AUTO_INCREMENT PRIMARY KEY,
                      titolo VARCHAR(255) NOT NULL,
                      genere VARCHAR(100) NOT NULL,
                      classificazione VARCHAR(50) NOT NULL,
                      durata INT NOT NULL,
                      locandina BLOB,  -- H2 non supporta MEDIUMBLOB, ma BLOB è sufficiente
                      descrizione TEXT NOT NULL,
                      is_proiettato BOOLEAN DEFAULT FALSE
);

CREATE TABLE slot (
                      id INT AUTO_INCREMENT PRIMARY KEY,
                      ora_inizio TIME NOT NULL
);

CREATE TABLE proiezione (
                            id INT AUTO_INCREMENT PRIMARY KEY,
                            data DATE NOT NULL,
                            id_film INT,
                            id_sala INT,
                            id_orario INT,
                            FOREIGN KEY (id_film) REFERENCES film(id)
                                ON DELETE CASCADE
                                ON UPDATE CASCADE,
                            FOREIGN KEY (id_sala) REFERENCES sala(id)
                                ON DELETE CASCADE
                                ON UPDATE CASCADE,
                            FOREIGN KEY (id_orario) REFERENCES slot(id)
                                ON DELETE CASCADE
                                ON UPDATE CASCADE
);

CREATE TABLE posto_proiezione (
                                  id_sala INT,
                                  fila CHAR(1),
                                  numero INT,
                                  id_proiezione INT,
                                  stato BOOLEAN DEFAULT TRUE,
                                  PRIMARY KEY (id_sala, fila, numero, id_proiezione),
                                  FOREIGN KEY (id_sala, fila, numero) REFERENCES posto(id_sala, fila, numero)
                                      ON DELETE CASCADE
                                      ON UPDATE CASCADE,
                                  FOREIGN KEY (id_proiezione) REFERENCES proiezione(id)
                                      ON DELETE CASCADE
                                      ON UPDATE CASCADE
);

CREATE TABLE prenotazione (
                              id INT AUTO_INCREMENT PRIMARY KEY,
                              email_cliente VARCHAR(255),
                              id_proiezione INT,
                              FOREIGN KEY (email_cliente) REFERENCES cliente(email)
                                  ON DELETE CASCADE
                                  ON UPDATE CASCADE,
                              FOREIGN KEY (id_proiezione) REFERENCES proiezione(id)
                                  ON DELETE CASCADE
                                  ON UPDATE CASCADE
);

CREATE TABLE occupa (
                        id_sala INT,
                        fila CHAR(1),
                        numero INT,
                        id_proiezione INT,
                        id_prenotazione INT,
                        PRIMARY KEY (id_sala, fila, numero, id_proiezione, id_prenotazione),
                        FOREIGN KEY (id_sala, fila, numero) REFERENCES posto(id_sala, fila, numero)
                            ON DELETE CASCADE
                            ON UPDATE CASCADE,
                        FOREIGN KEY (id_proiezione) REFERENCES proiezione(id)
                            ON DELETE CASCADE
                            ON UPDATE CASCADE,
                        FOREIGN KEY (id_prenotazione) REFERENCES prenotazione(id)
                            ON DELETE CASCADE
                            ON UPDATE CASCADE
);
