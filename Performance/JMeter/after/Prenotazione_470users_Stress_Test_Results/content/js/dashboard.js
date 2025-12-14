/*
   Licensed to the Apache Software Foundation (ASF) under one or more
   contributor license agreements.  See the NOTICE file distributed with
   this work for additional information regarding copyright ownership.
   The ASF licenses this file to You under the Apache License, Version 2.0
   (the "License"); you may not use this file except in compliance with
   the License.  You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
var showControllersOnly = false;
var seriesFilter = "";
var filtersOnlySampleSeries = true;

/*
 * Add header in statistics table to group metrics by category
 * format
 *
 */
function summaryTableHeader(header) {
    var newRow = header.insertRow(-1);
    newRow.className = "tablesorter-no-sort";
    var cell = document.createElement('th');
    cell.setAttribute("data-sorter", false);
    cell.colSpan = 1;
    cell.innerHTML = "Requests";
    newRow.appendChild(cell);

    cell = document.createElement('th');
    cell.setAttribute("data-sorter", false);
    cell.colSpan = 3;
    cell.innerHTML = "Executions";
    newRow.appendChild(cell);

    cell = document.createElement('th');
    cell.setAttribute("data-sorter", false);
    cell.colSpan = 7;
    cell.innerHTML = "Response Times (ms)";
    newRow.appendChild(cell);

    cell = document.createElement('th');
    cell.setAttribute("data-sorter", false);
    cell.colSpan = 1;
    cell.innerHTML = "Throughput";
    newRow.appendChild(cell);

    cell = document.createElement('th');
    cell.setAttribute("data-sorter", false);
    cell.colSpan = 2;
    cell.innerHTML = "Network (KB/sec)";
    newRow.appendChild(cell);
}

/*
 * Populates the table identified by id parameter with the specified data and
 * format
 *
 */
function createTable(table, info, formatter, defaultSorts, seriesIndex, headerCreator) {
    var tableRef = table[0];

    // Create header and populate it with data.titles array
    var header = tableRef.createTHead();

    // Call callback is available
    if(headerCreator) {
        headerCreator(header);
    }

    var newRow = header.insertRow(-1);
    for (var index = 0; index < info.titles.length; index++) {
        var cell = document.createElement('th');
        cell.innerHTML = info.titles[index];
        newRow.appendChild(cell);
    }

    var tBody;

    // Create overall body if defined
    if(info.overall){
        tBody = document.createElement('tbody');
        tBody.className = "tablesorter-no-sort";
        tableRef.appendChild(tBody);
        var newRow = tBody.insertRow(-1);
        var data = info.overall.data;
        for(var index=0;index < data.length; index++){
            var cell = newRow.insertCell(-1);
            cell.innerHTML = formatter ? formatter(index, data[index]): data[index];
        }
    }

    // Create regular body
    tBody = document.createElement('tbody');
    tableRef.appendChild(tBody);

    var regexp;
    if(seriesFilter) {
        regexp = new RegExp(seriesFilter, 'i');
    }
    // Populate body with data.items array
    for(var index=0; index < info.items.length; index++){
        var item = info.items[index];
        if((!regexp || filtersOnlySampleSeries && !info.supportsControllersDiscrimination || regexp.test(item.data[seriesIndex]))
                &&
                (!showControllersOnly || !info.supportsControllersDiscrimination || item.isController)){
            if(item.data.length > 0) {
                var newRow = tBody.insertRow(-1);
                for(var col=0; col < item.data.length; col++){
                    var cell = newRow.insertCell(-1);
                    cell.innerHTML = formatter ? formatter(col, item.data[col]) : item.data[col];
                }
            }
        }
    }

    // Add support of columns sort
    table.tablesorter({sortList : defaultSorts});
}

$(document).ready(function() {

    // Customize table sorter default options
    $.extend( $.tablesorter.defaults, {
        theme: 'blue',
        cssInfoBlock: "tablesorter-no-sort",
        widthFixed: true,
        widgets: ['zebra']
    });

    var data = {"OkPercent": 72.99635701275045, "KoPercent": 27.003642987249545};
    var dataset = [
        {
            "label" : "FAIL",
            "data" : data.KoPercent,
            "color" : "#FF6347"
        },
        {
            "label" : "PASS",
            "data" : data.OkPercent,
            "color" : "#9ACD32"
        }];
    $.plot($("#flot-requests-summary"), dataset, {
        series : {
            pie : {
                show : true,
                radius : 1,
                label : {
                    show : true,
                    radius : 3 / 4,
                    formatter : function(label, series) {
                        return '<div style="font-size:8pt;text-align:center;padding:2px;color:white;">'
                            + label
                            + '<br/>'
                            + Math.round10(series.percent, -2)
                            + '%</div>';
                    },
                    background : {
                        opacity : 0.5,
                        color : '#000'
                    }
                }
            }
        },
        legend : {
            show : true
        }
    });

    // Creates APDEX table
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [0.7299635701275046, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [0.6021276595744681, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [1.0, 500, 1500, "2. Login-0"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-0"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-1"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-0"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-1"], "isController": false}, {"data": [0.6021276595744681, 500, 1500, "2. Login"], "isController": false}, {"data": [0.9849624060150376, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-0"], "isController": false}, {"data": [0.6021276595744681, 500, 1500, "6. Checkout"], "isController": false}, {"data": [0.6021276595744681, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [0.5872340425531914, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [0.8914893617021277, 500, 1500, "1. Home Page"], "isController": false}, {"data": [0.597872340425532, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
        switch(index){
            case 0:
                item = item.toFixed(3);
                break;
            case 1:
            case 2:
                item = formatDuration(item);
                break;
        }
        return item;
    }, [[0, 0]], 3);

    // Create statistics table
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 4392, 1186, 27.003642987249545, 16274.185792349723, 0, 60137, 238.0, 60003.0, 60003.0, 60003.0, 5.609403157971369, 77.34720214533807, 1.2675040905889234], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 282, 0, 0.0, 0.3014184397163118, 0, 2, 0.0, 1.0, 1.0, 1.0, 1.3134973497163405, 9.116236000423859, 0.253977026605308], "isController": false}, {"data": ["3. Dettagli Film", 470, 187, 39.787234042553195, 23874.706382978726, 0, 60004, 4.0, 60003.0, 60003.0, 60004.0, 0.8733251203609249, 36.01696010158444, 0.15816678605206877], "isController": false}, {"data": ["2. Login-0", 282, 0, 0.0, 282.8404255319148, 219, 480, 282.0, 321.0, 332.5499999999999, 435.4000000000003, 1.3114876083023677, 0.2087621876496933, 0.4213666241518349], "isController": false}, {"data": ["6. Checkout-0", 1, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 1000.0, 160.15625, 249.0234375], "isController": false}, {"data": ["4. Proiezioni Film-1", 1, 0, 0.0, 2.0, 2, 2, 2.0, 2.0, 2.0, 2.0, 500.0, 2711.42578125, 97.16796875], "isController": false}, {"data": ["6. Checkout-1", 1, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 1000.0, 5422.8515625, 194.3359375], "isController": false}, {"data": ["5. Scelta Posto-0", 1, 0, 0.0, 0.0, 0, 0, 0.0, 0.0, 0.0, 0.0, Infinity, Infinity, Infinity], "isController": false}, {"data": ["5. Scelta Posto-1", 1, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 1000.0, 5422.8515625, 194.3359375], "isController": false}, {"data": ["2. Login", 470, 187, 39.787234042553195, 24043.168085106383, 4, 60003, 313.0, 60002.0, 60003.0, 60003.0, 0.9818196251120215, 5.206948841452842, 0.30382388714923453], "isController": false}, {"data": ["7. Completa Prenotazione-1", 266, 4, 1.5037593984962405, 1175.6992481203006, 0, 60002, 271.0, 327.50000000000006, 357.94999999999993, 60002.0, 0.9740985011333966, 7.574926164432222, 0.1939227903344527], "isController": false}, {"data": ["4. Proiezioni Film-0", 1, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 1000.0, 160.15625, 302.734375], "isController": false}, {"data": ["6. Checkout", 470, 187, 39.787234042553195, 23873.92127659574, 0, 60004, 2.0, 60003.0, 60003.0, 60003.29, 0.6544019671044663, 2.963336281332975, 0.0932354198893643], "isController": false}, {"data": ["4. Proiezioni Film", 470, 187, 39.787234042553195, 23878.980851063847, 3, 60011, 18.0, 60003.0, 60003.0, 60004.0, 0.7859978660994104, 4.702066306863601, 0.14360041216808314], "isController": false}, {"data": ["7. Completa Prenotazione", 470, 194, 41.276595744680854, 24924.246808510645, 1, 60137, 320.5, 60003.0, 60003.0, 60004.0, 0.6038437868971037, 3.376867900820585, 0.2084144346930097], "isController": false}, {"data": ["1. Home Page", 470, 51, 10.851063829787234, 6512.919148936172, 0, 60004, 2.0, 60002.0, 60003.0, 60003.29, 1.1219218760443421, 7.361768445768207, 0.14162725145253077], "isController": false}, {"data": ["5. Scelta Posto", 470, 189, 40.212765957446805, 24131.54893617021, 1, 60004, 10.0, 60003.0, 60003.0, 60003.0, 0.7141977963199059, 36.31814510675737, 0.1278916819320114], "isController": false}, {"data": ["7. Completa Prenotazione-0", 266, 0, 0.0, 4.041353383458646, 1, 135, 2.5, 7.0, 8.0, 9.0, 1.2483925772266913, 0.20965427504059622, 0.48713086474651995], "isController": false}]}, function(index, item){
        switch(index){
            // Errors pct
            case 3:
                item = item.toFixed(2) + '%';
                break;
            // Mean
            case 4:
            // Mean
            case 7:
            // Median
            case 8:
            // Percentile 1
            case 9:
            // Percentile 2
            case 10:
            // Percentile 3
            case 11:
            // Throughput
            case 12:
            // Kbytes/s
            case 13:
            // Sent Kbytes/s
                item = item.toFixed(2);
                break;
        }
        return item;
    }, [[0, 0]], 0, summaryTableHeader);

    // Create error table
    createTable($("#errorsTable"), {"supportsControllersDiscrimination": false, "titles": ["Type of error", "Number of errors", "% in errors", "% in all samples"], "items": [{"data": ["Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 1186, 100.0, 27.003642987249545], "isController": false}]}, function(index, item){
        switch(index){
            case 2:
            case 3:
                item = item.toFixed(2) + '%';
                break;
        }
        return item;
    }, [[1, 1]]);

        // Create top5 errors by sampler
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 4392, 1186, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 1186, "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": ["3. Dettagli Film", 470, 187, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 187, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": ["2. Login", 470, 187, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 187, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["7. Completa Prenotazione-1", 266, 4, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 4, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}, {"data": ["6. Checkout", 470, 187, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 187, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["4. Proiezioni Film", 470, 187, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 187, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["7. Completa Prenotazione", 470, 194, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 194, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["1. Home Page", 470, 51, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 51, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["5. Scelta Posto", 470, 189, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 189, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
