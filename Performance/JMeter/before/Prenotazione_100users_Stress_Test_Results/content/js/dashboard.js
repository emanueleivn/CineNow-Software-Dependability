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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [1.0, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [1.0, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [1.0, 500, 1500, "2. Login-0"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-0"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-1"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-0"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-1"], "isController": false}, {"data": [1.0, 500, 1500, "2. Login"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-0"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 1136, 0, 0.0, 30.600352112676074, 0, 137, 2.0, 96.0, 102.0, 112.62999999999988, 95.9297415977031, 5580.210482947348, 30.494776273011315], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 91, 0, 0.0, 0.41758241758241754, 0, 6, 0.0, 1.0, 1.0, 6.0, 9.311368054844982, 59.860093657270035, 1.8004403074797912], "isController": false}, {"data": ["3. Dettagli Film", 100, 0, 0.0, 1.11, 0, 12, 1.0, 2.0, 2.0, 11.909999999999954, 10.227040294538762, 678.3648760290959, 3.0761019635917366], "isController": false}, {"data": ["2. Login-0", 91, 0, 0.0, 90.5054945054945, 69, 128, 90.0, 103.0, 108.39999999999999, 128.0, 9.205867475973697, 1.465387107991907, 2.9577445308548307], "isController": false}, {"data": ["6. Checkout-0", 9, 0, 0.0, 0.4444444444444444, 0, 1, 0.0, 1.0, 1.0, 1.0, 1.028924202583743, 0.1647886418200526, 0.25622624185435006], "isController": false}, {"data": ["4. Proiezioni Film-1", 9, 0, 0.0, 0.0, 0, 0, 0.0, 0.0, 0.0, 0.0, 1.028924202583743, 5.473193487767235, 0.19995694952555162], "isController": false}, {"data": ["6. Checkout-1", 9, 0, 0.0, 0.1111111111111111, 0, 1, 0.0, 1.0, 1.0, 1.0, 1.0290418477018066, 5.473819281671621, 0.19997981219986277], "isController": false}, {"data": ["5. Scelta Posto-0", 9, 0, 0.0, 0.11111111111111113, 0, 1, 0.0, 1.0, 1.0, 1.0, 1.0291595197255574, 0.16482632933104632, 0.3055317324185249], "isController": false}, {"data": ["5. Scelta Posto-1", 9, 0, 0.0, 0.5555555555555556, 0, 1, 1.0, 1.0, 1.0, 1.0, 1.0292772186642267, 5.4750712988906685, 0.20002555323650503], "isController": false}, {"data": ["2. Login", 100, 0, 0.0, 82.89, 0, 129, 88.5, 102.9, 107.89999999999998, 128.93999999999997, 10.116337885685383, 61.52482059307031, 5.020529052857865], "isController": false}, {"data": ["7. Completa Prenotazione-1", 100, 0, 0.0, 83.97000000000001, 0, 135, 88.5, 105.9, 109.94999999999999, 134.98, 10.117361392148927, 2346.8839119726326, 2.0380950273168756], "isController": false}, {"data": ["4. Proiezioni Film-0", 9, 0, 0.0, 0.4444444444444444, 0, 1, 0.0, 1.0, 1.0, 1.0, 1.02880658436214, 0.164769804526749, 0.31145511831275724], "isController": false}, {"data": ["6. Checkout", 100, 0, 0.0, 0.6300000000000002, 0, 3, 1.0, 1.0, 1.0, 2.989999999999995, 10.225994477962981, 67.4481230506698, 2.599040354330709], "isController": false}, {"data": ["4. Proiezioni Film", 100, 0, 0.0, 4.659999999999997, 0, 11, 5.0, 7.0, 8.0, 10.969999999999985, 10.224948875255624, 115.07241340746423, 3.2742802594580778], "isController": false}, {"data": ["7. Completa Prenotazione", 100, 0, 0.0, 85.90000000000002, 0, 137, 91.0, 107.9, 112.94999999999999, 136.96999999999997, 10.115314586283633, 2348.101067007637, 5.992434851051994], "isController": false}, {"data": ["1. Home Page", 100, 0, 0.0, 1.0600000000000007, 0, 13, 1.0, 1.0, 2.0, 12.899999999999949, 10.199918400652795, 66.60825619645043, 1.4443243829049368], "isController": false}, {"data": ["5. Scelta Posto", 100, 0, 0.0, 2.5999999999999996, 0, 10, 2.0, 4.0, 6.0, 9.989999999999995, 10.227040294538762, 943.7020407739312, 3.233202885303743], "isController": false}, {"data": ["7. Completa Prenotazione-0", 100, 0, 0.0, 1.9100000000000008, 0, 6, 2.0, 3.0, 3.0, 5.97999999999999, 10.230179028132993, 1.7111572890025575, 3.9996603260869565], "isController": false}]}, function(index, item){
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
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 1136, 0, "", "", "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
