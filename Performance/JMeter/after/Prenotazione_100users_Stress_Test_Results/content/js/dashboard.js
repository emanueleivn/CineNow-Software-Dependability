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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [0.9981549815498155, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [1.0, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [0.99, 500, 1500, "2. Login-0"], "isController": false}, {"data": [0.99, 500, 1500, "2. Login"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 1084, 0, 0.0, 48.823800738007336, 0, 730, 5.0, 145.5, 161.0, 205.30000000000018, 24.05681313803817, 445.8232772969374, 7.612527914169995], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 100, 0, 0.0, 0.5099999999999999, 0, 2, 0.0, 1.0, 1.9499999999999886, 2.0, 2.588326646822829, 17.964099100556492, 0.500477222725508], "isController": false}, {"data": ["3. Dettagli Film", 100, 0, 0.0, 3.7800000000000007, 0, 151, 2.0, 5.0, 5.949999999999989, 149.5899999999993, 2.5524529072438615, 170.41112837561897, 0.7677299760069427], "isController": false}, {"data": ["2. Login-0", 100, 0, 0.0, 138.83999999999995, 89, 728, 115.0, 168.9, 206.79999999999995, 726.3999999999992, 2.541942043721403, 0.40462554016268426, 0.8166981761565836], "isController": false}, {"data": ["2. Login", 100, 0, 0.0, 139.51999999999998, 90, 730, 115.5, 169.9, 208.79999999999995, 728.3999999999992, 2.541877430670293, 18.046336836887725, 1.308173248010981], "isController": false}, {"data": ["7. Completa Prenotazione-1", 92, 0, 0.0, 118.6413043478261, 88, 199, 111.5, 153.7, 160.35, 199.0, 2.223672443380949, 17.470515002235757, 0.44951190994126605], "isController": false}, {"data": ["6. Checkout", 100, 0, 0.0, 1.8900000000000003, 0, 52, 1.0, 3.0, 3.9499999999999886, 51.52999999999976, 2.459238128027937, 14.245208904593857, 0.5801064158448713], "isController": false}, {"data": ["4. Proiezioni Film", 100, 0, 0.0, 10.989999999999998, 4, 106, 6.0, 19.900000000000006, 22.94999999999999, 106.0, 2.526209422761147, 20.75488268914993, 0.7647704307187065], "isController": false}, {"data": ["7. Completa Prenotazione", 100, 0, 0.0, 113.58000000000001, 2, 204, 113.0, 160.9, 168.74999999999994, 203.75999999999988, 2.416626389560174, 18.09116251057274, 1.3923685581802803], "isController": false}, {"data": ["1. Home Page", 100, 0, 0.0, 1.9900000000000002, 0, 19, 1.0, 4.0, 4.0, 18.87999999999994, 2.5587226856353307, 18.01850516222302, 0.36231913029015916], "isController": false}, {"data": ["5. Scelta Posto", 100, 0, 0.0, 5.58, 2, 68, 3.5, 10.0, 11.949999999999989, 67.44999999999972, 2.4931438544003988, 209.4390572410247, 0.7450215033657442], "isController": false}, {"data": ["7. Completa Prenotazione-0", 92, 0, 0.0, 3.7173913043478257, 1, 10, 3.0, 7.0, 8.349999999999994, 10.0, 2.23127667830811, 0.3747847545595654, 0.8705266464760381], "isController": false}]}, function(index, item){
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
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 1084, 0, "", "", "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
