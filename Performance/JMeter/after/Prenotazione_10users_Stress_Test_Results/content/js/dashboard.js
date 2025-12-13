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

    var data = {"OkPercent": 100.0, "KoPercent": 0.0};
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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [0.990909090909091, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [1.0, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [0.95, 500, 1500, "2. Login-0"], "isController": false}, {"data": [0.95, 500, 1500, "2. Login"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 110, 0, 0.0, 69.5636363636364, 0, 579, 12.5, 167.9, 191.79999999999995, 578.78, 8.449189645902143, 155.28018845053384, 2.682602710461633], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 10, 0, 0.0, 0.8999999999999999, 0, 1, 1.0, 1.0, 1.0, 1.0, 1.2344155042587335, 8.567374012467596, 0.2386858103937785], "isController": false}, {"data": ["3. Dettagli Film", 10, 0, 0.0, 19.7, 1, 138, 7.5, 125.30000000000004, 138.0, 138.0, 1.2531328320802004, 83.66374921679197, 0.3769188596491228], "isController": false}, {"data": ["2. Login-0", 10, 0, 0.0, 191.7, 120, 577, 154.5, 537.1000000000001, 577.0, 577.0, 1.1523392486748099, 0.183429001498041, 0.37023399688868397], "isController": false}, {"data": ["2. Login", 10, 0, 0.0, 192.79999999999998, 121, 579, 155.5, 539.0000000000001, 579.0, 579.0, 1.1522064754003918, 8.180215894688327, 0.5929812622421938], "isController": false}, {"data": ["7. Completa Prenotazione-1", 10, 0, 0.0, 146.0, 99, 194, 148.0, 193.6, 194.0, 194.0, 1.108278842956888, 8.707673272470354, 0.22403683641804278], "isController": false}, {"data": ["6. Checkout", 10, 0, 0.0, 9.1, 1, 61, 4.0, 55.50000000000002, 61.0, 61.0, 1.187789523696401, 6.879783636714574, 0.2796641153937522], "isController": false}, {"data": ["4. Proiezioni Film", 10, 0, 0.0, 20.7, 6, 54, 20.0, 51.20000000000001, 54.0, 54.0, 1.2467273407305821, 10.242887810123426, 0.3774272222914848], "isController": false}, {"data": ["7. Completa Prenotazione", 10, 0, 0.0, 153.4, 103, 205, 156.0, 204.7, 205.0, 205.0, 1.1069293779056897, 8.883000159121098, 0.6551854452623422], "isController": false}, {"data": ["1. Home Page", 10, 0, 0.0, 5.0, 2, 19, 2.5, 17.700000000000003, 19.0, 19.0, 1.141682840506907, 8.039721643452449, 0.16166407409521635], "isController": false}, {"data": ["5. Scelta Posto", 10, 0, 0.0, 18.7, 4, 92, 11.5, 84.30000000000003, 92.0, 92.0, 1.2283503255128363, 103.30018386868934, 0.3670656246161405], "isController": false}, {"data": ["7. Completa Prenotazione-0", 10, 0, 0.0, 7.2, 3, 11, 7.0, 11.0, 11.0, 11.0, 1.1191941801902632, 0.18798964745383323, 0.43620155987688863], "isController": false}]}, function(index, item){
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
    createTable($("#errorsTable"), {"supportsControllersDiscrimination": false, "titles": ["Type of error", "Number of errors", "% in errors", "% in all samples"], "items": []}, function(index, item){
        switch(index){
            case 2:
            case 3:
                item = item.toFixed(2) + '%';
                break;
        }
        return item;
    }, [[1, 1]]);

        // Create top5 errors by sampler
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 110, 0, "", "", "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
