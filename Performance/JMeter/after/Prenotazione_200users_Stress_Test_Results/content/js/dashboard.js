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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [1.0, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [1.0, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [1.0, 500, 1500, "2. Login-0"], "isController": false}, {"data": [1.0, 500, 1500, "2. Login"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 2184, 0, 0.0, 52.47481684981678, 0, 258, 5.0, 162.0, 172.0, 187.0, 17.49649509313038, 322.48103595033047, 5.546968881434007], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 200, 0, 0.0, 0.41999999999999976, 0, 7, 0.0, 1.0, 1.0, 2.980000000000018, 1.6720590571258975, 11.60480831932984, 0.32330829424895285], "isController": false}, {"data": ["3. Dettagli Film", 200, 0, 0.0, 2.5350000000000006, 0, 9, 2.0, 5.0, 5.0, 8.0, 1.6646690637901185, 111.13941915534691, 0.5007012418431216], "isController": false}, {"data": ["2. Login-0", 200, 0, 0.0, 142.27999999999997, 93, 258, 146.0, 176.0, 181.0, 199.93000000000006, 1.6696441988212312, 0.2657734418045514, 0.536438419347837], "isController": false}, {"data": ["2. Login", 200, 0, 0.0, 142.80499999999998, 94, 258, 146.5, 176.9, 182.0, 202.9000000000001, 1.669630260378839, 11.853722649369297, 0.8592726047066876], "isController": false}, {"data": ["7. Completa Prenotazione-1", 192, 0, 0.0, 134.07291666666669, 91, 217, 126.0, 171.0, 179.7, 200.25999999999988, 1.5644861640754864, 12.292318535901698, 0.3162584335582282], "isController": false}, {"data": ["6. Checkout", 200, 0, 0.0, 1.3000000000000003, 0, 4, 1.0, 3.0, 3.0, 3.990000000000009, 1.6403795838356996, 9.50194679736391, 0.3869469614018684], "isController": false}, {"data": ["4. Proiezioni Film", 200, 0, 0.0, 10.910000000000005, 3, 29, 8.0, 21.0, 22.0, 28.99000000000001, 1.657399043680752, 13.616892728990395, 0.50175166361429], "isController": false}, {"data": ["7. Completa Prenotazione", 200, 0, 0.0, 132.955, 3, 223, 127.5, 177.9, 186.95, 201.96000000000004, 1.6295934164425976, 12.638833720361768, 0.9520867707569461], "isController": false}, {"data": ["1. Home Page", 200, 0, 0.0, 1.955, 0, 18, 2.0, 4.0, 4.0, 5.0, 1.6761789823917397, 11.803639298854332, 0.23734956293633033], "isController": false}, {"data": ["5. Scelta Posto", 200, 0, 0.0, 5.314999999999997, 1, 17, 4.0, 10.0, 11.0, 13.0, 1.6491989016335316, 138.19521786432864, 0.49282701552720765], "isController": false}, {"data": ["7. Completa Prenotazione-0", 192, 0, 0.0, 4.0, 1, 9, 3.0, 8.0, 8.0, 9.0, 1.5663495896490398, 0.26309778263636213, 0.6111382905170585], "isController": false}]}, function(index, item){
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
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 2184, 0, "", "", "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
