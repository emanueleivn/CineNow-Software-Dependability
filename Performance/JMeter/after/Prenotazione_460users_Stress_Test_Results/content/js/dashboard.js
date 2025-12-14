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
    createTable($("#apdexTable"), {"supportsControllersDiscrimination": true, "overall": {"data": [0.9994033412887828, 500, 1500, "Total"], "isController": false}, "titles": ["Apdex", "T (Toleration threshold)", "F (Frustration threshold)", "Label"], "items": [{"data": [1.0, 500, 1500, "2. Login-1"], "isController": false}, {"data": [1.0, 500, 1500, "3. Dettagli Film"], "isController": false}, {"data": [0.9989082969432315, 500, 1500, "2. Login-0"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-0"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-1"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout-1"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-0"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto-1"], "isController": false}, {"data": [0.9989130434782608, 500, 1500, "2. Login"], "isController": false}, {"data": [0.9977272727272727, 500, 1500, "7. Completa Prenotazione-1"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film-0"], "isController": false}, {"data": [1.0, 500, 1500, "6. Checkout"], "isController": false}, {"data": [1.0, 500, 1500, "4. Proiezioni Film"], "isController": false}, {"data": [0.9978260869565218, 500, 1500, "7. Completa Prenotazione"], "isController": false}, {"data": [1.0, 500, 1500, "1. Home Page"], "isController": false}, {"data": [1.0, 500, 1500, "5. Scelta Posto"], "isController": false}, {"data": [1.0, 500, 1500, "7. Completa Prenotazione-0"], "isController": false}]}, function(index, item){
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
    createTable($("#statisticsTable"), {"supportsControllersDiscrimination": true, "overall": {"data": ["Total", 5028, 0, 0.0, 94.11933174224333, 0, 758, 5.0, 279.0, 291.0, 316.0, 13.823288447051967, 253.7388967409907, 4.381998482235645], "isController": false}, "titles": ["Label", "#Samples", "FAIL", "Error %", "Average", "Min", "Max", "Median", "90th pct", "95th pct", "99th pct", "Transactions/s", "Received", "Sent"], "items": [{"data": ["2. Login-1", 458, 0, 0.0, 0.441048034934498, 0, 7, 0.0, 1.0, 1.0, 1.4099999999999682, 1.2766087918765314, 8.860213558463387, 0.2468442781167512], "isController": false}, {"data": ["3. Dettagli Film", 460, 0, 0.0, 2.849999999999999, 0, 133, 2.0, 5.0, 6.0, 10.0, 1.280905321604696, 85.51796978768995, 0.38527230376391247], "isController": false}, {"data": ["2. Login-0", 458, 0, 0.0, 257.9999999999997, 195, 756, 253.0, 297.1, 308.0, 389.8699999999966, 1.2739207832665778, 0.20278231218012907, 0.4092968141549844], "isController": false}, {"data": ["6. Checkout-0", 2, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 0.012671862130140023, 0.002029477919280238, 0.003155590667173541], "isController": false}, {"data": ["4. Proiezioni Film-1", 2, 0, 0.0, 25.0, 2, 48, 25.0, 48.0, 48.0, 48.0, 0.01268126280014964, 0.0687686057902646, 0.002464425094950955], "isController": false}, {"data": ["6. Checkout-1", 2, 0, 0.0, 0.5, 0, 1, 0.5, 1.0, 1.0, 1.0, 0.012671862130140023, 0.0687176273522144, 0.0024625982069315083], "isController": false}, {"data": ["5. Scelta Posto-0", 2, 0, 0.0, 0.0, 0, 0, 0.0, 0.0, 0.0, 0.0, 0.012678609917208677, 0.002030558619552952, 0.0037639623191713257], "isController": false}, {"data": ["5. Scelta Posto-1", 2, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 0.01267852954414347, 0.06875378374866083, 0.0024638939250825687], "isController": false}, {"data": ["2. Login", 460, 0, 0.0, 257.43695652173886, 1, 758, 253.0, 297.90000000000003, 308.9, 389.1199999999985, 1.2794837561192702, 9.051353410450044, 0.6573489044420339], "isController": false}, {"data": ["7. Completa Prenotazione-1", 440, 0, 0.0, 252.8363636363636, 0, 519, 249.0, 293.0, 302.0, 342.7699999999999, 1.2205981485745356, 9.576851650858996, 0.24669866344502733], "isController": false}, {"data": ["4. Proiezioni Film-0", 2, 0, 0.0, 1.0, 1, 1, 1.0, 1.0, 1.0, 1.0, 0.0126814236166152, 0.002031009251098528, 0.0038391028526862424], "isController": false}, {"data": ["6. Checkout", 460, 0, 0.0, 1.4282608695652168, 0, 51, 1.0, 3.0, 4.0, 5.0, 1.2782571241993526, 7.403174953628444, 0.3026769804301613], "isController": false}, {"data": ["4. Proiezioni Film", 460, 0, 0.0, 10.739130434782611, 3, 101, 7.0, 21.0, 22.0, 28.389999999999986, 1.280128235454543, 10.502649917626531, 0.38862045137043294], "isController": false}, {"data": ["7. Completa Prenotazione", 460, 0, 0.0, 245.8130434782609, 0, 528, 248.0, 298.90000000000003, 307.0, 347.0, 1.2760480237899736, 9.853374973646835, 0.7446584343653603], "isController": false}, {"data": ["1. Home Page", 460, 0, 0.0, 1.8434782608695668, 0, 19, 1.0, 3.0, 4.0, 6.0, 1.280855388642154, 9.019773640135325, 0.18137112436827377], "isController": false}, {"data": ["5. Scelta Posto", 460, 0, 0.0, 5.7652173913043505, 1, 83, 4.0, 11.0, 12.0, 15.0, 1.2792417989476847, 106.47536533998631, 0.3833434461800727], "isController": false}, {"data": ["7. Completa Prenotazione-0", 440, 0, 0.0, 3.768181818181818, 0, 11, 3.0, 7.0, 8.0, 9.589999999999975, 1.221631766868236, 0.20515257903124604, 0.4767091522083771], "isController": false}]}, function(index, item){
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
    createTable($("#top5ErrorsBySamplerTable"), {"supportsControllersDiscrimination": false, "overall": {"data": ["Total", 5028, 0, "", "", "", "", "", "", "", "", "", ""], "isController": false}, "titles": ["Sample", "#Samples", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors", "Error", "#Errors"], "items": [{"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}, {"data": [], "isController": false}]}, function(index, item){
        return item;
    }, [[0, 0]], 0);

});
