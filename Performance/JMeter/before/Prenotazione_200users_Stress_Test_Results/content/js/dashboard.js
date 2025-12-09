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

    var data = {"OkPercent": 61.24567474048443, "KoPercent": 38.75432525951557};
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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [0.6113033448673587, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [0.45, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [0.9888888888888889, 500, 1500, "2. Login-0"], "isController": false}, {"data": [0.445, 500, 1500, "2. Login"], "isController": false}, {"data": [0.961038961038961, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [0.45, 500, 1500, "6. Checkout"], "isController": false}, {"data": [0.45, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [0.41, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [0.445, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 1734, 672, 38.75432525951557, 23280.749711649365, 0, 60132, 111.0, 60003.0, 60003.0, 60004.0, 3.57566321954036, 124.81394676522595, 0.6520653276402478], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 90, 0, 0.0, 0.6333333333333334, 0, 2, 1.0, 1.0, 1.0, 2.0, 1.713991887105068, 11.018758391418613, 0.33141640004570644], "isController": false}, {"data": ["3. Dettagli Film", 200, 110, 55.0, 33003.695, 1, 60017, 60002.0, 60003.0, 60003.0, 60004.0, 0.8342440497543151, 26.101369972115393, 0.11291623564057429], "isController": false}, {"data": ["2. Login-0", 90, 0, 0.0, 134.6777777777777, 83, 596, 127.0, 156.9, 180.85000000000002, 596.0, 1.6947875866224766, 0.269775758417445, 0.544516714842573], "isController": false}, {"data": ["2. Login", 200, 110, 55.0, 33062.079999999994, 84, 60014, 60001.0, 60002.0, 60002.95, 60004.0, 1.1122728182768669, 4.897856424348764, 0.25759326059995996], "isController": false}, {"data": ["7. Completa Prenotazione-1", 77, 3, 3.896103896103896, 2458.090909090909, 83, 60002, 120.0, 189.20000000000002, 6265.59999999966, 60002.0, 0.685858837781024, 176.756612107858, 0.13324352776392204], "isController": false}, {"data": ["6. Checkout", 200, 110, 55.0, 33002.14000000001, 0, 60006, 60002.0, 60003.0, 60003.0, 60004.0, 0.47506502452523186, 2.1172984722205728, 0.050417667519804275], "isController": false}, {"data": ["4. Proiezioni Film", 200, 110, 55.0, 33006.939999999995, 4, 60008, 60002.0, 60003.0, 60003.0, 60005.98, 0.6665000416562525, 4.389137090727318, 0.09079761309672582], "isController": false}, {"data": ["7. Completa Prenotazione", 200, 118, 59.0, 35450.884999999995, 2, 60132, 60002.0, 60003.0, 60003.95, 60086.35, 0.415379854492437, 41.882513426504765, 0.09994672104335112], "isController": false}, {"data": ["1. Home Page", 200, 0, 0.0, 2.705, 0, 18, 2.0, 5.0, 5.949999999999989, 16.960000000000036, 1.6730661446700297, 10.925579403719226, 0.23690878025112724], "isController": false}, {"data": ["5. Scelta Posto", 200, 111, 55.5, 33305.59499999999, 2, 60014, 60002.0, 60003.0, 60003.0, 60005.98, 0.5547296247808817, 25.682256223199627, 0.07376712207657488], "isController": false}, {"data": ["7. Completa Prenotazione-0", 77, 0, 0.0, 7.285714285714286, 1, 131, 4.0, 9.0, 11.099999999999937, 131.0, 1.4729230828088833, 0.24740504906555463, 0.5746133576907626], "isController": false}]}, function(index, item){
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
    createTable($("#errorsTable"), {"supportsControllersDiscrimination": false, "titles": ["Type of error", "Number of errors", "% in errors", "% in all samples"], "items": [{"data": ["Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 672, 100.0, 38.75432525951557], "isController": false}]}, function(index, item){
        switch(index){
            case 2:
            case 3:
                item = item.toFixed(2) + '%';
                break;
        }
        return item;
    }, [[1, 1]]);

        // Create top5 errors by sampler
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 1734, 672, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 672, "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": ["3. Dettagli Film", 200, 110, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 110, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}, {"data": ["2. Login", 200, 110, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 110, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["7. Completa Prenotazione-1", 77, 3, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 3, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["6. Checkout", 200, 110, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 110, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["4. Proiezioni Film", 200, 110, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 110, "", "", "", "", "", "", "", ""], "isController": false}, {"data": ["7. Completa Prenotazione", 200, 118, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 118, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}, {"data": ["5. Scelta Posto", 200, 111, "Non HTTP response code: java.net.SocketTimeoutException/Non HTTP response message: Read timed out", 111, "", "", "", "", "", "", "", ""], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
