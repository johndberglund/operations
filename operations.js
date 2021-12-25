// points are stored as point index and mapping. 
// Like [2,[0,1]] is point 2 translated by 0 vectorA and 1 vectorB.
// halfkite = [center, vertex1, vertex2]
// kite = [center1, vertex1, center2, vertex2]
// poly = [vertex1, vertex2, ... vertexN]
// halfkiteDeg = [center, vertex1, vertex2, degree of center]
// flag = [center, vertex, midpoint]

var Ax;
var Ay;
var Bx;
var By;
var tiles = {
  pts : [],
  polys : []
};
var comList = "";
var midpoints = [];
var pointList = [];
var polyList = [];
var myTiling;
var sized=1;

function init() {
  sized=1;
  xOffset=0;
  yOffset=0;
  pointList = [];
  curPoly = [];
  polyList = [];
  mode = 0;
  squares();
  var d = document.getElementById("canvasDiv");
  d.style.maxHeight= window.innerHeight-170 + "px";
  d.style.height = window.innerHeight-170 + "px";
  d.style.maxWidth= window.innerWidth-170 + "px";
  draw();
}

function resize() {
  var d = document.getElementById("canvasDiv");
  d.style.maxHeight= window.innerHeight-170 + "px";
  d.style.height = window.innerHeight-170 + "px";
  d.style.maxWidth= window.innerWidth-170 + "px";
  draw(); 
}

function mapping(rawPt, mapping) {
  var X = rawPt[0]+mapping[0]*Ax + mapping[1]*Bx;
  var Y = rawPt[1]+mapping[0]*Ay + mapping[1]*By;
  return  [X,Y] ;
}

function invMap(rawPt, mapping) {
  var X = rawPt[0]-mapping[0]*Ax - mapping[1]*Bx;
  var Y = rawPt[1]-mapping[0]*Ay - mapping[1]*By;
  return  [X,Y] ;
}

function avePts(ptList) {
  var xSum=0;
  var ySum=0;
  ptList.forEach(function(pt) {
    xSum+= pt[0];
    ySum+= pt[1];
  });
  xSum /= ptList.length;
  ySum /= ptList.length;
  return [xSum, ySum];
}

function avePtMap(ptMapList) {
  var XSum=0;
  var YSum=0;
  ptMapList.forEach(function(PtMap) {
    var newPt = mapping(tiles.pts[PtMap[0]], PtMap[1]);
    XSum+= newPt[0];
    YSum+= newPt[1];
  });
  var Xave = XSum / ptMapList.length;
  var Yave = YSum / ptMapList.length;
  return [Xave, Yave];
}

function composeMaps(maps) {
  var map0 = 0;
  var map1 = 0;
  maps.forEach(function(oldMap) {
    map0 += oldMap[0];
    map1 += oldMap[1];
  });
  return [map0, map1];
}

// find which translation parallelogram rawPt is in
function transPara(rawPt) {
  var denom = Ax*By-Ay*Bx;
  var M = floor((rawPt[0]*By - rawPt[1]*Bx)/denom);
  var N = floor((rawPt[1]*Ax - rawPt[0]*Ay)/denom);
  return([M,N]);
}

// input polygon and center, average the polar coordinates to find best fit regular polygon, 
// output vote where to move tiles.pts
function avePolar(polyRawPolar,centPt) {
  var rNew = 0;
  var tBase = 0;
  var vertNum = 0;
  var numVert = polyRawPolar.length;
  polyRawPolar.forEach(function(ptMapRawPolar) {
    vertNum += 1;
    rNew += ptMapRawPolar[3][0];
    var addBaseT = ptMapRawPolar[3][1] + vertNum*2*Math.PI/numVert;
    addBaseT %= (2*Math.PI);
    addBaseT += (2*Math.PI);
    addBaseT %= (2*Math.PI);
    if (addBaseT>Math.PI) {addBaseT -= (2*Math.PI)};
    tBase += addBaseT;
  });
  tBase /= numVert;
  rNew /= numVert;
  var PtVoteList = [];
  var maxDist = rNew*numVert*2;
  var bestCount = 10;
  for (counter = -2;counter<3;counter++) {
    var sumDist = 0;
    vertNum = 0;
    polyRawPolar.forEach(function(ptMapRawPolar) {
      vertNum += 1;
      var tNew = tBase - (vertNum+counter)*2*Math.PI/numVert;
      var newX = centPt[0] + rNew*Math.cos(tNew);
      var newY = centPt[1] + rNew*Math.sin(tNew);
      var thisDist = Math.sqrt((newX-ptMapRawPolar[2][0])**2+(newY-ptMapRawPolar[2][1])**2);
      sumDist += thisDist;
    });
    if (sumDist<maxDist) {maxDist = sumDist; bestCount=counter;};
  } // end counter
  vertNum = 0;
  polyRawPolar.forEach(function(ptMapRawPolar) {
    vertNum += 1;
    var tNew = tBase - (vertNum+bestCount)*2*Math.PI/numVert;
    var newX = centPt[0] + rNew*Math.cos(tNew);
    var newY = centPt[1] + rNew*Math.sin(tNew);
    var newPt = invMap([newX,newY], ptMapRawPolar[1]);
    PtVoteList.push([ptMapRawPolar[0],newPt]);
  });
  return (PtVoteList);
} //

function rect2Polar(rect) {
  var x = rect[0];
  var y = rect[1];
  var radius = Math.sqrt(x*x+y*y);
  var theta;
  if (x === 0) {
    if (y < 0) { theta = 3*Math.PI/2; }
      else { theta = Math.PI/2;}
    } 
    else { theta = Math.atan(y/x);}
  if (x < 0) {theta += Math.PI;}
  if (theta < 0) {theta +=2*Math.PI;}
  return [radius, theta];
}

function addPolar(polyRaw, centPt) {
  var polyRawPolar = [];
  polyRaw.forEach(function(ptMapRaw) {
    var vecX = ptMapRaw[2][0]-centPt[0];
    var vecY = ptMapRaw[2][1]-centPt[1];
    var vecPolar = rect2Polar([vecX, vecY]);
    polyRawPolar.push([ptMapRaw[0],ptMapRaw[1],ptMapRaw[2],vecPolar]);
  });
  return polyRawPolar;
}

function polyRaw2Cent(polyRaw) {
  var rawPtList = [];
  polyRaw.forEach(function(ptMapRaw) {
    rawPtList.push(ptMapRaw[2]);
  });
  var centPt = avePts(rawPtList);
  return centPt ;
}

function polyAddRaw(poly) {
  var polyRaw = [];
  poly.forEach(function(ptMap) {
    var rawPt = mapping(tiles.pts[ptMap[0]],ptMap[1]);
    polyRaw.push([ptMap[0],ptMap[1],rawPt]);
  });
  return polyRaw;
}

// this will try to make the polygons regular
// it some times makes funny stuff happen around 2:00 on big polygons
// this can be fixed at times by a couple of duals
function makeRegular() {
  var PtVoteList = [];
  tiles.polys.forEach(function(poly) {
    var polyRaw = polyAddRaw(poly);
    var centPt = polyRaw2Cent(polyRaw);
    var polyRawPolar = addPolar(polyRaw, centPt);
    // sort by descending angle so all polygons have same orientation
    polyRawPolar.sort((A,B)=> B[3][1]-A[3][1]);
    PtVoteList = PtVoteList.concat(avePolar(polyRawPolar,centPt));
  });
  // sort point list by index
  PtVoteList.sort((A,B) => A[0]-B[0]);
  var curPt = 0;
  var votesByPt = [];
  var avePtVote=[];
  // average all votes for where to move the point
  PtVoteList.forEach(function(ptVote) {
    if (curPt === ptVote[0]) {votesByPt.push(ptVote[1]);}
    else { 
      avePtVote.push([curPt,avePts(votesByPt)]);
      curPt = ptVote[0];
      votesByPt = [ptVote[1]];
      };
  });
  avePtVote.push([curPt,avePts(votesByPt)]);
  // don't move any fixed points - currently none.
//  var fixedPts = [];
//  for (counter = 0;counter<tiles.pts.length;counter++) {
//    if (tiles.pts[counter][0]===0) {fixedPts[counter]=[counter,tiles.pts[counter]] }
//  }; 
  for (i = 0;i<avePtVote.length;i++) {
    tiles.pts[avePtVote[i][0]] = avePtVote[i][1];
  }
  // fixedPts.forEach(function(fixedPt) {tiles.pts[fixedPt[0]]=fixedPt[1];});
} // end makeRegular

function makeRegular10Draw() {
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  makeRegular();
  draw();
}

function polys2halfkites() {
  var halfkites = [];
  tiles.polys.forEach(function(poly) {
    var centPt = avePtMap(poly);
    var centPtNum = tiles.pts.length;
    tiles.pts.push(centPt);
    var lastPtMap = poly[poly.length-1];
    poly.forEach(function(ptMap) {
      halfkites.push([[centPtNum,[0,0]],lastPtMap,ptMap]);
      lastPtMap = ptMap;
    });   
  });
  return(halfkites);
}

function polys2halfkiteDegs() {
  var halfkiteDegs = [];
  tiles.polys.forEach(function(poly) {
    var centPt = avePtMap(poly);
    var centPtNum = tiles.pts.length;
    tiles.pts.push(centPt);
    var lastPtMap = poly[poly.length-1];
    var degree = poly.length;
    poly.forEach(function(ptMap) {
      halfkiteDegs.push([[centPtNum,[0,0]],lastPtMap,ptMap,degree]);
      lastPtMap = ptMap;
    });   
  });
  return(halfkiteDegs);
}

function polys2kites() {
  var halfkites = polys2halfkites();
  var newHalfkites = [];
  // if needed trade so that vertex 1 < vertex 2. translate halfkite so vertex 1 in box
  halfkites.forEach(function(halfkite) {
    var vert1 = halfkite[1];
    var vert2 = halfkite[2];
    var trade = compare(vert1,vert2);
    if (trade===1) 
      {halfkite[1]=vert2;
       halfkite[2]=vert1;
      };
    var invA = -halfkite[1][1][0];
    var invB = -halfkite[1][1][1];
    var map0= composeMaps([[invA,invB],halfkite[0][1]]);
    var map1= composeMaps([[invA,invB],halfkite[1][1]]);
    var map2= composeMaps([[invA,invB],halfkite[2][1]]);
    var cent1 = [halfkite[0][0],map0];
    vert1 = [halfkite[1][0],map1];
    vert2 = [halfkite[2][0],map2];
    newHalfkites.push([cent1,vert1,vert2]);
  });
  // ugly hack to sort so that matching pairs will be adjacent
  newHalfkites.sort((A,B)=> A[2][1][1]-B[2][1][1]);
  newHalfkites.sort((A,B)=> A[2][1][0]-B[2][1][0]); 
  newHalfkites.sort((A,B)=> A[2][0]-B[2][0]); 
  newHalfkites.sort((A,B)=> A[1][1][1]-B[1][1][1]);
  newHalfkites.sort((A,B)=> A[1][1][0]-B[1][1][0]); 
  newHalfkites.sort((A,B)=> A[1][0]-B[1][0]); 
  var kites = [];
  var counter = 0;
  var oldCent = [];
  var oldVert1 = [];
  var oldVert2 = [];
  newHalfkites.forEach(function(halfkite) {
    if (counter ===0) 
      {oldCent = halfkite[0];
       oldVert1 = halfkite[1];
       oldVert2 = halfkite[2];
  var raw1 = mapping(tiles.pts[oldCent[0]],oldCent[1]);
  var raw2 = mapping(tiles.pts[oldVert1[0]],oldVert1[1]);
  var raw3 = mapping(tiles.pts[oldVert2[0]],oldVert2[1]);
  var orient = (raw2[1]-raw1[1])*(raw3[0]-raw2[0])-(raw3[1]-raw2[1])*(raw2[0]-raw1[0]);
  if (orient < 0) {oldVert2 = halfkite[1];oldVert1=halfkite[2];}
       counter = 1;
      }
    else
  { //    {if (JSON.stringify(oldVert1) != JSON.stringify(halfkite[1])) 
    //       {alert([oldVert1,halfkite[1],"Error! vertices don't match"]);};
    //   if (JSON.stringify(oldVert2) != JSON.stringify(halfkite[2])) 
     //      {alert([oldVert2,halfkite[2],"Error! vertices don't match"]);};
       kites.push([halfkite[0],oldVert1,oldCent,oldVert2]);
       counter=0;
      }
  });
  return(kites);
} // end polys2kites

function dualKites(kites) {
  var newKites = [];
  kites.forEach(function(kite) {
    newKites.push([kite[1],kite[2],kite[3],kite[0]]);
  });
  return (newKites);
}

function kites2halfkites(kites) {
  var halfkites = [];
  kites.forEach(function(kite) {
    halfkites.push([kite[0],kite[1],kite[3]]);
    halfkites.push([kite[2],kite[1],kite[3]]);
  }); 
  return(halfkites);
}

function halfkites2polys(halfkites) {
  var polys = [];
  var newHalfkites = [];
  // sort by center
  halfkites.sort((A,B)=> A[0][0]-B[0][0]);
  // translate to make center in box
  halfkites.forEach(function(halfkite) {
    var invA = -halfkite[0][1][0];
    var invB = -halfkite[0][1][1];
    var map0= composeMaps([[invA,invB],halfkite[0][1]]);
    var map1= composeMaps([[invA,invB],halfkite[1][1]]);
    var map2= composeMaps([[invA,invB],halfkite[2][1]]);
    var cent1 = [halfkite[0][0],map0];
    var vert1 = [halfkite[1][0],map1];
    var vert2 = [halfkite[2][0],map2];
    newHalfkites.push([cent1,vert1,vert2]);
  });
  var oldCent = newHalfkites[0][0];
  var currentList = [];
  newHalfkites.forEach(function(halfkite) {
    if (JSON.stringify(oldCent)===JSON.stringify(halfkite[0])) 
      {currentList.push(halfkite)}
    else
      {
//alert(currentList);
       var newPoly = makePoly(currentList);
       polys.push(newPoly);
       oldCent = halfkite[0];
       currentList = [];
       currentList.push(halfkite);
      }   
  });
//alert(currentList);
  var newPoly = makePoly(currentList);
  polys.push(newPoly);
  return(polys);
} // end halfkites2polys

function flags2halfkites(flags) {
  var halfkites = [];
  var newflags = [];
  // sort by midpoint
  flags.sort((A,B)=> A[2][0]-B[2][0]);
  // sort by center
  flags.sort((A,B)=> A[0][0]-B[0][0]);
  // translate to make center in box
  flags.forEach(function(flag) {
    var invA = -flag[0][1][0];
    var invB = -flag[0][1][1];
    var map0= composeMaps([[invA,invB],flag[0][1]]);
    var map1= composeMaps([[invA,invB],flag[1][1]]);
    var map2= composeMaps([[invA,invB],flag[2][1]]);
    var cent = [flag[0][0],map0];
    var vert = [flag[1][0],map1];
    var mid  = [flag[2][0],map2];
    newflags.push([cent,vert,mid]);
  });
//alert(JSON.stringify(newflags));
  var oldCent = newflags[0][0];
  var oldMid = newflags[0][2];
  var currentList = [];
  newflags.forEach(function(flag) {
    if ((JSON.stringify(oldCent)===JSON.stringify(flag[0])) && 
        (JSON.stringify(oldMid)===JSON.stringify(flag[2]))) 
      {currentList.push(flag)}
    else
      { 
       var newHalfkite = makeHalfkite(currentList);
       halfkites.push(newHalfkite);
       oldCent = flag[0];
       oldMid = flag[2];
       currentList = [];
       currentList.push(flag);
      }   
  });
  var newHalfkite = makeHalfkite(currentList);
  halfkites.push(newHalfkite);
  return(halfkites);
} // end flags2halfkites

function makeHalfkite(flags) {
  var cent = flags[0][0];
  var vert1 = flags[0][1];
  var vert2 = flags[1][1];
  return([cent,vert1,vert2]);
}

function makePoly(halfkites) {
  var poly = [];
  var used = [];
  for (i=0;i<halfkites.length;i++) {
    used.push(0);
  }
  poly.push(halfkites[0][1]);
  used[0] = 1;
  var nextPt = JSON.stringify(halfkites[0][2]);
  for (i=1;i<halfkites.length;i++) {
    var nextIndex = halfkites.findIndex((halfkite, index) => 
           JSON.stringify(halfkite[1])===nextPt && used[index]===0);
    if (nextIndex >=0) 
      {poly.push(halfkites[nextIndex][1]);
       nextPt = JSON.stringify(halfkites[nextIndex][2]);
       used[nextIndex]=1;
      }
    else
      {nextIndex = halfkites.findIndex((halfkite, index) => 
           JSON.stringify(halfkite[2])===nextPt && used[index]===0);
       if (nextIndex<0) {alert([i,"Error: point not found."])};
       poly.push(halfkites[nextIndex][2]);
       nextPt = JSON.stringify(halfkites[nextIndex][1]);
       used[nextIndex]=1;
      }
  } // end for loop
  return(poly);
} // end makePoly

function findMid(pt1,pt2) {
  // makes copies
  var P1 = JSON.parse(JSON.stringify(pt1));
  var P2 = JSON.parse(JSON.stringify(pt2));
  var trade = compare(P1,P2);
  if (trade===1) 
    {P1=JSON.parse(JSON.stringify(pt2));
     P2=JSON.parse(JSON.stringify(pt1));
    };
  // move P1 into parallelogram
  var unmap = [-P1[1][0],-P1[1][1]];
  P1[1] = [0,0];
  P2[1] = composeMaps([unmap,P2[1]]);
  var nextIndex = midpoints.findIndex((midPt) =>
       JSON.stringify(P1)===midPt[0] && JSON.stringify(P2)===midPt[1]);
  if (nextIndex < 0)
    {midpoints.push([JSON.stringify(P1),JSON.stringify(P2),tiles.pts.length]);
     tiles.pts.push(avePtMap([P1,P2]));
     return[tiles.pts.length-1,[-unmap[0],-unmap[1]]];
    }
  else // repeated point
    {return[midpoints[nextIndex][2],[-unmap[0],-unmap[1]]];
     }
} // end findMid

function compare(vert1, vert2) {
  var trade = 0;
  if (vert1[0]>vert2[0]) 
    {trade = 1}
  else { 
    if (vert1[0]===vert2[0]) 
      {if (vert1[1][0]>vert2[1][0]) 
         {trade = 1;}
       else {
         if (vert1[1][0]===vert2[1][0])
           {if (vert1[1][1]>vert2[1][1])
             {trade = 1}
           }
         }
      }
  }
  return trade;
} // end compare

function dual() {
  dualNoDraw();
  comList += "D";
  makeRegular10Draw();
} // end dual

function dualNoDraw() {
  var kites = polys2kites();
  kites = dualKites(kites);
  var halfkites = kites2halfkites(kites);
  tiles.polys =halfkites2polys(halfkites);
} // end dualNoDraw

function f2a() {
  tiles.polys=polys2kites();
  comList += "2";
  makeRegular10Draw();
} 

function f3a() {
  tiles.polys = polys2halfkites();
  comList += "3";
  makeRegular10Draw();
}

function f4a() {
  tiles.polys=polys2kites();
  tiles.polys=polys2kites();
  comList += "4a";
  dualNoDraw()
  makeRegular10Draw();
} 

function f4b() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([V1,A1,A2,V2,A4,A3]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "4b";
  makeRegular10Draw();
} // end f4b


function f5a() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([A1,A2,V2,V1]);
    polys.push([A3,A4,V2,V1]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "5a";
  makeRegular10Draw();
} // end f5a

function f5b() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A3);
    var B2 = findMid(C2,A2);

    halfkites.push([A1,V1,B1]);
    halfkites.push([A1,B1,C1]);
    halfkites.push([A2,C1,B1]);
    halfkites.push([A2,B1,B2]);
    halfkites.push([A2,B2,V2]);
    halfkites.push([A3,C2,B2]);
    halfkites.push([A3,B2,B1]);
    halfkites.push([A3,B1,V1]);
    halfkites.push([A4,V2,B2]);
    halfkites.push([A4,B2,C2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "5b";
  dualNoDraw()
  makeRegular10Draw();
} // end f5b

function f5c() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([A1,V1,A3,A2]);
    polys.push([A2,A3,A4,V2]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A4,A3]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "5c";
  makeRegular10Draw();
} // end f5c

function f5d() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V2,V1);
    var M1 = findMid(C1,M);
    var M2 = findMid(C2,M);
    polys.push([V1,M1,M2]);
    polys.push([V2,M1,M2]);
    halfkites.push([C1,V1,M1]);
    halfkites.push([C1,V2,M1]);
    halfkites.push([C2,V1,M2]);
    halfkites.push([C2,V2,M2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "5d";
  makeRegular10Draw();
} // end f5d

function f6a1() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([V1,A1,A2,V2,A4,A3]);
    polys.push([C1,A1,A2]);
    polys.push([C2,A4,A3]);
  });
  tiles.polys=polys;
  comList += "6a1.";
  makeRegular10Draw();
} // end f6a1

function f6a2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(A1,V1);
    var B2 = findMid(A2,V2);
    var B3 = findMid(A3,V1);
    var B4 = findMid(A4,V2);
    polys.push([B1,A1,A2,B2,B4,A4,A3,B3]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
    halfkites.push([V1,B1,B3]);
    halfkites.push([V2,B2,B4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "6a2.";
  makeRegular10Draw();
} // end f6a2

function f6b() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([A1,A2,A4,A3]);
    polys.push([C1,A1,A2]);
    polys.push([C2,A3,A4]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "6b";
  dualNoDraw()
  makeRegular10Draw();
} // end f6b

function f6c1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V2,V1);
    var M1 = findMid(C1,M);
    var M2 = findMid(C2,M);
    polys.push([M1,V2,M2,V1]);
    halfkites.push([A1,V1,M1]);
    halfkites.push([A1,M1,C1]);
    halfkites.push([A2,V2,M1]);
    halfkites.push([A2,M1,C1]);
    halfkites.push([A3,V1,M2]);
    halfkites.push([A3,M2,C2]);
    halfkites.push([A4,V2,M2]);
    halfkites.push([A4,M2,C2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "6c1.";
  dualNoDraw()
  makeRegular10Draw();
} // end f6c1

function f6c2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V2,V1);
    polys.push([V1,A1,M,A3]);
    polys.push([V2,A2,M,A4]);
    halfkites.push([C1,A1,M]);
    halfkites.push([C1,A2,M]);
    halfkites.push([C2,A3,M]);
    halfkites.push([C2,A4,M]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "6c2.";
  makeRegular10Draw();
} // end f6c2

function f6d() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V2,V1);
    polys.push([V1,C1,M]);
    polys.push([V2,C1,M]);
    polys.push([V1,C2,M]);
    polys.push([V2,C2,M]);
  });
  tiles.polys=polys;
  comList += "6d";
  dualNoDraw()
  makeRegular10Draw();
} // end f6d

function f7a() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([V1,A1,A2,V2]);
    polys.push([C1,A1,A2]);
    polys.push([V1,A3,A4,V2]);
    polys.push([C2,A3,A4]);
  });
  tiles.polys=polys;
  comList += "7a";
  makeRegular10Draw();
} // end f7a

function f7b() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([C1,A1,A2]);
    polys.push([C2,A3,A4]);
    polys.push([A1,A2,A4]);
    polys.push([A1,A3,A4]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7b";
  dualNoDraw()
  makeRegular10Draw();
} // end f7b

function f7c() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([C1,A1,A2]);
    polys.push([C2,A3,A4]);
    polys.push([V1,A1,A2,A3]);
    polys.push([V2,A2,A3,A4]);
  });
  tiles.polys=polys;
  comList += "7c";
  dualNoDraw()
  makeRegular10Draw();
} // end f7c

function f7d() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  dualNoDraw()
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    var B1 = findMid(M,V1);
    var B2 = findMid(M,V2);
    polys.push([C1,A1,B1,B2,A2]);
    polys.push([C2,A3,B1,B2,A4]);
    halfkites.push([V1,A1,B1]);
    halfkites.push([V1,A3,B1]);
    halfkites.push([V2,A2,B2]);
    halfkites.push([V2,A4,B2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7d";
  makeRegular10Draw();
} // end f7d


function f7e1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V1,V2);
    var M1 = findMid(M,V1);
    var M2 = findMid(M,V2);
    var B1 = findMid(M,C1);
    var B2 = findMid(M,C2);
    polys.push([M1,B1,B2]);
    polys.push([M2,B1,B2]);
    halfkites.push([C1,V1,M1]);
    halfkites.push([C1,B1,M1]);
    halfkites.push([C1,B1,M2]);
    halfkites.push([C1,V2,M2]);
    halfkites.push([C2,V1,M1]);
    halfkites.push([C2,B2,M1]);
    halfkites.push([C2,B2,M2]);
    halfkites.push([C2,V2,M2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7e1.";
 // makeRegular10Draw();
draw();
} // end f7e1

function f7e2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(A1,A2);
    var B2 = findMid(A3,A4);
    polys.push([V1,B1,V2]);
    polys.push([V1,B2,V2]);
    halfkites.push([A1,V1,B1]);
    halfkites.push([A1,B1,C1]);
    halfkites.push([A2,V2,B1]);
    halfkites.push([A2,B1,C1]);
    halfkites.push([A3,V1,B2]);
    halfkites.push([A3,B2,C2]);
    halfkites.push([A4,V2,B2]);
    halfkites.push([A4,B2,C2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7e2.";
  dualNoDraw()
  makeRegular10Draw();
} // end f7e2

function f7e3() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V1,V2);
    var B1 = findMid(M,C1);
    var B2 = findMid(M,C2);
    polys.push([V1,B1,V2,C1]);
    polys.push([V1,B2,V2,C2]);
    polys.push([V1,B1,B2]);
    polys.push([V2,B1,B2]);
  });
  tiles.polys=polys;
  comList += "7e3.";
  dualNoDraw(); 
  dualNoDraw();
  dualNoDraw();
  makeRegular10Draw();
} // end f7e3


function f7e4() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(A1,A2);
    var B2 = findMid(A3,A4);
    polys.push([C1,A1,B1,A2]);
    polys.push([C2,A3,B2,A4]);
    halfkites.push([V1,A1,B1]);
    halfkites.push([V1,B1,B2]);
    halfkites.push([V1,B2,A3]);
    halfkites.push([V2,A2,B1]);
    halfkites.push([V2,B1,B2]);
    halfkites.push([V2,B2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7e4.";
  makeRegular10Draw();
} // end f7e4

function f7f() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M1 = findMid(A1,A3);
    var M2 = findMid(A2,A4);
    polys.push([M1,A1,A2,M2]);
    polys.push([M1,A3,A4,M2]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
    halfkites.push([V1,A1,M1]);
    halfkites.push([V1,M1,A3]);
    halfkites.push([V2,A2,M2]);
    halfkites.push([V2,M2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "7f";
  makeRegular10Draw();
} // end f7f

function f7g() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V1,V2);
    var M1 = findMid(M,V1);
    var M2 = findMid(M,V2);
    polys.push([C1,V1,M1,M2]);
    polys.push([M2,V2,C1]);
    polys.push([C2,V2,M2,M1]);
    polys.push([M1,V1,C2]);
  });
  tiles.polys=polys;
  comList += "7g";
  dualNoDraw()
  makeRegular10Draw();
} // end f7g

function f8a() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    polys.push([A1,A2,A4,A3]);
    polys.push([A1,A2,B2,B1]);
    polys.push([A3,A4,B4,B3]);
    halfkites.push([C1,B1,B2]);
    halfkites.push([C2,B3,B4]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8a";
  dualNoDraw()
  makeRegular10Draw();
} // end f8a

function f8b() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    polys.push([A1,A2,A4,A3]);
    polys.push([C1,A1,A2]);
    polys.push([C2,A3,A4]);
    polys.push([V1,A1,A3]);
    polys.push([V2,A2,A4]);
  });
  tiles.polys=polys;
  comList += "8b";
  makeRegular10Draw();
} // end f8b

function f8c1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    polys.push([A1,B1,B2,A2,A4,B4,B3,A3]);
    polys.push([C1,B1,B2]);
    polys.push([C2,B3,B4]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8c1.";
  makeRegular10Draw();
} // end f8c1

function f8c2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    polys.push([A1,B1,B2,A2]);
    polys.push([A4,B4,B3,A3]);
    polys.push([V1,A1,A2,V2,A4,A3]);
    halfkites.push([C1,B1,B2]);
    halfkites.push([C2,B3,B4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8c2.";
  makeRegular10Draw();
} // end f8c2

function f8d1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([A1,A2,C1]);
    polys.push([A1,A2,M]);
    polys.push([A3,A4,C2]);
    polys.push([A3,A4,M]);
    halfkites.push([V1,A1,M]);
    halfkites.push([V1,A3,M]);
    halfkites.push([V2,A2,M]);
    halfkites.push([V2,A4,M]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8d1.";
  dualNoDraw()
  makeRegular10Draw();
} // end f8d1

function f8d2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    var M = findMid(V1,V2);
    polys.push([A1,B1,B2,A2,M]);
    polys.push([A3,B3,B4,A4,M]);
    halfkites.push([C1,B1,B2]);
    halfkites.push([C2,B3,B4]);
    halfkites.push([V1,A1,M]);
    halfkites.push([V1,A3,M]);
    halfkites.push([V2,A2,M]);
    halfkites.push([V2,A4,M]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8d2.";
  makeRegular10Draw();
} // end f8d2

function f8e() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([A1,A2,M]);
    polys.push([A2,A4,M]);
    polys.push([A4,A3,M]);
    polys.push([A1,A3,M]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8e";
  makeRegular10Draw();
} // end f8e

function f8f() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([A1,A2,M]);
    polys.push([A4,A3,M]);
    polys.push([V1,A1,M,A3]);
    polys.push([V2,A2,M,A4]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8f";
  makeRegular10Draw();
} // end f8f

function f8g1() {
  var polys = [];
  var halfkites = [];
  var flags = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    var D1 = findMid(V1,A1);
    var D2 = findMid(V2,A2);
    var D3 = findMid(V1,A3);
    var D4 = findMid(V2,A4);
    var M = findMid(V1,V2);
    polys.push([B1,M,B2,C1]);
    polys.push([B3,M,B4,C2]);
    halfkites.push([A1,B1,M]);
    halfkites.push([A2,B2,M]);
    halfkites.push([A3,B3,M]);
    halfkites.push([A4,B4,M]);
    flags.push([A1,M,D1]);
    flags.push([V1,M,D1]);
    flags.push([A2,M,D2]);
    flags.push([V2,M,D2]);
    flags.push([A3,M,D3]);
    flags.push([V1,M,D3]);
    flags.push([A4,M,D4]);
    flags.push([V2,M,D4]);
  });
  var newHalfkites = flags2halfkites(flags);
  halfkites = halfkites.concat(newHalfkites);
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8g1.";
  dualNoDraw()
  makeRegular10Draw();
} // end f8g1


function f8g2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  dualNoDraw();
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var D1 = findMid(V1,A1);
    var D2 = findMid(V2,A2);
    var D3 = findMid(V1,A3);
    var D4 = findMid(V2,A4);
    var M1 = findMid(A1,A3);
    var M2 = findMid(A2,A4);
    polys.push([A1,A2,M2,A4,A3,M1]);
    halfkites.push([C1,A1,A2]);
    halfkites.push([C2,A3,A4]);
    halfkites.push([D1,V1,M1]);
    halfkites.push([D1,M1,A1]);
    halfkites.push([D2,V2,M2]);
    halfkites.push([D2,M2,A2]);
    halfkites.push([D3,V1,M1]);
    halfkites.push([D3,M1,A3]);
    halfkites.push([D4,V2,M2]);
    halfkites.push([D4,M2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8g2.";
  makeRegular10Draw();
} // end f8g2

function f8h1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(C1,A1);
    var B2 = findMid(C1,A2);
    var B3 = findMid(C2,A3);
    var B4 = findMid(C2,A4);
    var D1 = findMid(A1,A2);
    var D2 = findMid(A3,A4);
    polys.push([V1,A1,D1,A2,V2,A4,D2,A3]);
    halfkites.push([B1,A1,D1]);
    halfkites.push([B1,D1,C1]);
    halfkites.push([B2,A2,D1]);
    halfkites.push([B2,D1,C1]);
    halfkites.push([B3,A3,D2]);
    halfkites.push([B3,D2,C2]);
    halfkites.push([B4,A4,D2]);
    halfkites.push([B4,D2,C2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8h1.";
  makeRegular10Draw();
} // end f8h1

function f8h2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var B1 = findMid(V1,A1);
    var B2 = findMid(V2,A2);
    var B3 = findMid(V1,A3);
    var B4 = findMid(V2,A4);
    var M = findMid(V1,V2);
    polys.push([C1,A1,M,A2]);
    polys.push([C2,A3,M,A4]);
    halfkites.push([B1,V1,M]);
    halfkites.push([B1,M,A1]);
    halfkites.push([B2,V2,M]);
    halfkites.push([B2,M,A2]);
    halfkites.push([B3,V1,M]);
    halfkites.push([B3,M,A3]);
    halfkites.push([B4,V2,M]);
    halfkites.push([B4,M,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8h2.";
  dualNoDraw()
  makeRegular10Draw();
} // end f8h2

function f8i() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([C1,A1,M,A2]);
    polys.push([C2,A3,M,A4]);
    polys.push([V1,A1,M,A3]);
    polys.push([V2,A2,M,A4]);
  });
  tiles.polys=polys;
  comList += "8i";
  dualNoDraw()
  makeRegular10Draw();
} // end f8i

function f8j() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([C1,A1,M]);
    polys.push([C1,A2,V2,A4,M]);
    polys.push([C2,A4,M]);
    polys.push([C2,A3,V1,A1,M]);
  });
  tiles.polys=polys;
  comList += "8j";
  dualNoDraw()
  makeRegular10Draw();
} // end f8j

function f8k() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M = findMid(V1,V2);
    polys.push([C1,A1,M]);
    polys.push([C1,A2,A4,M]);
    polys.push([C2,A4,M]);
    polys.push([C2,A3,A1,M]);
    halfkites.push([V1,A1,A3]);
    halfkites.push([V2,A2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8k";
  dualNoDraw()
  makeRegular10Draw();
} // end f8k

function f8L1() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var A1 = findMid(C1,V1);
    var A2 = findMid(C1,V2);
    var A3 = findMid(C2,V1);
    var A4 = findMid(C2,V2);
    var M1 = findMid(A1,A3);
    var M2 = findMid(A2,A4);
    polys.push([C1,A2,M2]);
    polys.push([C1,M2,A4,C2,M1,A1]);
    polys.push([C2,A3,M1]);
    halfkites.push([V1,A1,M1]);
    halfkites.push([V1,M1,A3]);
    halfkites.push([V2,A2,M2]);
    halfkites.push([V2,M2,A4]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8L1.";
  dualNoDraw()
  makeRegular10Draw();
} // end f8L1

function f8L2() {
  var polys = [];
  var halfkites = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V1,V2);
    var D1 = findMid(C1,M);
    var D2 = findMid(C2,M);
    polys.push([V1,M,D1]);
    polys.push([V1,M,D2]);
    polys.push([V2,M,D1]);
    polys.push([V2,M,D2]);
    halfkites.push([C1,V1,D1]);
    halfkites.push([C1,V2,D1]);
    halfkites.push([C2,V1,D2]);
    halfkites.push([C2,V2,D2]);
  });
  var newPolys = halfkites2polys(halfkites);
  polys = polys.concat(newPolys);
  tiles.polys=polys;
  comList += "8L2.";
  makeRegular10Draw();
} // end f8L2

function f8L3() {
  var polys = [];
  midpoints = [];
  var kites = polys2kites();
  kites.forEach(function(kite) {
    var C1 = kite[0];
    var V1 = kite[1];
    var C2 = kite[2];
    var V2 = kite[3];
    var M = findMid(V1,V2);
    var D1 = findMid(C1,M);
    var D2 = findMid(C2,M);
    polys.push([V1,C1,D1]);
    polys.push([V2,C1,D1]);
    polys.push([V1,C2,D2]);
    polys.push([V2,C2,D2]);
    polys.push([V1,D1,V2,D2]);
  });
  tiles.polys=polys;
  comList += "8L3.";
  dualNoDraw()
  makeRegular10Draw();
} // end f8L3

function txtToFile(content, filename, contentType) {
  const a = document.createElement('a');
  const file = new Blob([content], {type: "text/plain", endings: "native"});
  a.href= URL.createObjectURL(file);
  a.download = filename;
  a.click();
  URL.revokeObjectURL(a.href);
};

function goSave() {
  asOutput = "vectors:\r\n";
  asOutput = asOutput.concat(""+Ax+","+Ay+"\r\n");
  asOutput = asOutput.concat(""+Bx+","+By+"\r\n");
  asOutput = asOutput.concat("points:"+"\r\n");
  tiles.pts.forEach(function(point) {
    asOutput = asOutput.concat(""+point[0]+","+point[1]+"\r\n");
  });
  tiles.polys.forEach(function(poly) {
    asOutput = asOutput.concat("poly:"+"\r\n");
    poly.forEach(function(ptMap) {
      asOutput = asOutput.concat(""+ptMap[0]+","+ptMap[1][0]+","+ptMap[1][1]+"\r\n");
    });
  });
  asOutput = asOutput.concat("end"+"\r\n");
  txtToFile(asOutput,"myTiles","txt");
}

function svgToFile(content, filename, contentType) {
  const a = document.createElement('a');
  const file = new Blob([content], {type: "image/svg+xml", endings: "native"});
  a.href= URL.createObjectURL(file);
  a.download = filename;
  a.click();
  URL.revokeObjectURL(a.href);
};

function goSvg() {
  var asOutput = '<svg height="600" width="600">\r\n';
  tiles.polys.forEach(function(poly) {
    for (i = 0;i<3;i++) {
      for (j = 0;j<3;j++) {
        asOutput = asOutput.concat('<polygon points="\r\n'); 
        poly.forEach(function(ptMap) {
          var newPoint = mapping(tiles.pts[ptMap[0]],ptMap[1]);
          var sPoint = "" + (newPoint[0]+i*Ax+j*Bx) + "," + (newPoint[1]+i*Ay+j*By) + "\r\n";
          asOutput = asOutput.concat(sPoint);
        });
        var red = 80*(1+poly.length-3*Math.round(poly.length/3));
        var green = 50*(1+poly.length-5*Math.round(poly.length/5));
        var blue = 30*(1+poly.length-7*Math.round(poly.length/7));
        asOutput = asOutput.concat('" style="fill:rgb(',red,",",green,",",blue,');stroke:black;stroke-width:1" />\r\n'); 
      } 
    } 
  });
  asOutput = asOutput.concat('</svg>');
  svgToFile(asOutput,"myTiles","svg");
}

// init square tiling
function squares() {
  tiles.pts = [[1,1]];
  tiles.polys = [
    [[0,[0,0]],[0,[1,0]],[0,[1,1]],[0,[0,1]]]
  ];
  var size = window.innerHeight-15;
  if (size > window.innerWidth - 200) {size = window.innerWidth - 200};
  Ax=size/2-10;
  Ay=0;
  Bx=0;
  By=Ax;
  comList = "S";
  draw();
}

// init triangle tiling
function triangles() {
  tiles.pts = [[2,1]];
  tiles.polys = [
    [[0,[0,0]],[0,[0,1]],[0,[1,0]]],
    [[0,[1,0]],[0,[0,1]],[0,[1,1]]]
  ];
  var size = window.innerHeight-15;
  if (size > window.innerWidth - 200) {size = window.innerWidth - 200};
  Ax=size/1.8-10;
  Ay=0;
  Bx=Ax/2;
  By=Bx*Math.sqrt(3);
  comList = "T";
}

// init hexagon tiling 
function hexagons() {
  triangles();
  dual();
  comList = "H";
  draw();
}

function loadTiling() {
  var c = document.getElementById("myCanvas");
  var context = c.getContext("2d");
  const file = document.getElementById("loadTiling").files[0];
  const reader = new FileReader();
  reader.addEventListener("load", function () {
    var lines = reader.result.split(/\r\n|\n/);
    init();
    tiles.pts = [];
    tiles.polys = [];
    var curLen = lines.length;
    var setPoly = 0;
    for (i = 1;i<curLen;i++) {
      if (lines[i] === "points:") { setPoly = 1; continue;}
      if (lines[i] === "poly:") { setPoly = 2; curPoly = []; continue;}
      if (lines[i] === "end") { comList = "["+file.name+"]"; draw(); break;}
      var coords = lines[i].split(",");
      if (i===1) {Ax = coords[0],Ay=coords[1]}
      if (i===2) {Bx = coords[0],By=coords[1]}
      if (setPoly === 1) {tiles.pts.push([parseFloat(coords[0]),parseFloat(coords[1])]);}
      if (setPoly === 2) {
        curPoly.push( [parseInt(coords[0]),[parseInt(coords[1]),parseInt(coords[2])]] );
        if (lines[i+1] === "poly:") {tiles.polys.push(curPoly);curPoly = [];};
        if (lines[i+1] === "end") {tiles.polys.push(curPoly);curPoly = [];};
      }
    }
  },false);
  if (file) {
    reader.readAsText(file);
  }
} // end loadTiling()

function draw() {
  var c = document.getElementById("myCanvas");
  var context = c.getContext("2d");
  c.height = window.innerHeight-135;
  c.width = window.innerWidth-195;
  context.rect(0,0,c.width,c.height);
  context.fillStyle = "white";
  context.fill();
  context.lineWidth =1;
  document.getElementById("commandList").innerHTML =comList;

  tiles.polys.forEach(function(poly) {
    for (i = -2;i<5;i++) {
      for (j = -2;j<5;j++) {
        context.beginPath();
        context.strokeStyle ="black";
        var red = 80*(1+poly.length-3*Math.round(poly.length/3));
        var green = 50*(1+poly.length-5*Math.round(poly.length/5));
        var blue = 30*(1+poly.length-7*Math.round(poly.length/7));
        context.fillStyle = "rgb("+red+","+green+","+blue+")";
        var ptMap1 = poly[0];
        var newPoint = mapping(tiles.pts[ptMap1[0]],ptMap1[1]);
        context.moveTo(
         (newPoint[0]+200+i*Ax+j*Bx)*sized,
         (newPoint[1]+15+i*Ay+j*By)*sized
        );
        poly.forEach(function(ptMap) {
          var newPoint = mapping(tiles.pts[ptMap[0]],ptMap[1]);
          context.lineTo(
           (newPoint[0]+200+i*Ax+j*Bx)*sized,
           (newPoint[1]+15+i*Ay+j*By)*sized
          );	
        });
        context.closePath();
        context.fill();
        context.stroke();
      } // end j loop
    } // end i loop
  });
}
