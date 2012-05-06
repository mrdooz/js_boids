var boid_size = 10;
var MAX_SPEED = 0.1;
var MAX_FORCE = 0.1;
var NUM_BOIDS = 50;
//var path = [    new vector2(250, 400), new vector2(500,550), new vector2(900,300), new vector2(900,100), new vector2(150, 100) ];
var path = [new vector2(250, 400)];
var path_width = 20;
var boids = [];
var debugDraw = false;
var useSpline = true;

var spline_x = [];
var spline_y = [];

var coeff_x;
var coeff_y;


function bracket(func, x1, x2) {
    // from numerical recipes in C
    // Given a function func and an initial guessed range x1 to x2, the routine expands the range
    // geometrically until a root is bracketed by the returned values x1 and x2 (in which case zbrac
    // returns 1) or until the range becomes unacceptably large (in which case zbrac returns 0).

    var FACTOR = 1.6;
    var NTRY = 50;
    
    if (x1 == x2) {
        console.log("Bad initial range in zbrac");
        return { res: false };
    }
    
    var f1=func(x1);
    var f2=func(x2);
    for (var j=1;j<=NTRY;j++) {
        if (f1*f2 < 0.0) 
            return { res: true, x1: x1, x2: x2 };
        if (Math.abs(f1) < Math.abs(f2)) {
            x1 += FACTOR*(x1-x2);
            f1 = func(x1);
        } else {
            x2 += FACTOR*(x2-x1);
            f2 = func(x2);
        }
    }
    
    return { res: false };
}

function ridder(func, x1, x2, xacc) {
    // from numerical recipes in C
    // Using Ridders’ method, return the root of a function func known to lie between x1 and x2.
    // The root, returned as zriddr, will be refined to an approximate accuracy xacc.

    var UNUSED = -1.11e30;
    var MAXIT = 60;
    
    var SIGN = function(a, b) {
        return (b) >= 0.0 ? Math.abs(a) : -Math.abs(a);
    };

    var ans,fh,fl,fm,fnew,s,xh,xl,xm,xnew;
    fl=func(x1);
    fh=func(x2);
    if ((fl > 0.0 && fh < 0.0) || (fl < 0.0 && fh > 0.0)) {
        xl=x1;
        xh=x2;
        ans=UNUSED; // Any highly unlikely value, to simplify logic below.
        
        for (var j=1;j<=MAXIT;j++) {
            xm=0.5*(xl+xh);
            fm=func(xm); // First of two function evaluations per iteration.
            s=Math.sqrt(fm*fm-fl*fh); 
            if (s == 0.0) 
                return ans;
            xnew=xm+(xm-xl)*((fl >= fh ? 1.0 : -1.0)*fm/s); // Updating formula.
            if (Math.abs(xnew-ans) <= xacc) 
                return ans;
            ans=xnew;
            fnew=func(ans); // Second of two function evaluations per iteration.
            if (fnew == 0.0) 
                return ans;
            if (SIGN(fm,fnew) != fm) { // Bookkeeping to keep the root bracketed on next iteration.
                xl=xm; 
                fl=fm;
                xh=ans;
                fh=fnew;
            } else if (SIGN(fl,fnew) != fl) {
                xh=ans;
                fh=fnew;
            } else if (SIGN(fh,fnew) != fh) {
                xl=ans;
                fl=fnew;
            } else {
                console.log("never get here.");
            }
            if (Math.abs(xh-xl) <= xacc) 
                return ans;
        }
        console.log("zriddr exceed maximum iterations");
    } else {
        if (fl == 0.0) return x1;
        if (fh == 0.0) return x2;
        console.log("root must be bracketed in zriddr.");
    }
    return 0.0;     // Never get here.
}

function evalSpline(a, b, c, d, x, x0) {
    var dx = x - x0;
    var dx2 = dx * dx;
    var dx3 = dx2 * dx;
    return a + b * dx + c * dx2 + d * dx3;
}

function makeSpline(a, b, c, d, x0) {
    var f = function(t) {
        return evalSpline(a, b, c, d, t, x0);
    };
    return f;
}

function calcSpline(xs, ys) {
    // natural boundary conditions
    // from http://banach.millersville.edu/~bob/math375/
    var n = xs.length-1;
    a = []; b = []; c = []; d = [];
    
    h = [];
    for (var i = 0; i <= n-1; ++i) {
        a[i] = ys[i];
        h[i] = xs[i+1] - xs[i];
    }
    a[n] = ys[n];
    
    alpha = [];
    for (var i = 1; i <= n-1; ++i) {
        alpha[i] = 3/h[i] * (a[i+1] - a[i]) - 3/h[i-1]*(a[i]-a[i-1]);
    }
    
    l = [];
    u = [];
    z = [];
    l[0] = 1;
    u[0] = 0;
    z[0] = 0;
    for (var i = 1; i <= n-1; ++i) {
        l[i] = 2*(xs[i+1] - xs[i-1]) - h[i-1]*u[i-1];
        u[i] = h[i] / l[i];
        z[i] = (alpha[i] - h[i-1] * z[i-1]) / l[i];
    }
    
    l[n] = 1;
    c[n] = 0;
    z[n] = 0;
    for (var j = n-1; j >= 0; --j) {
        c[j] = z[j] - u[j] * c[j+1];
        b[j] = (a[j+1] - a[j]) / h[j] - (h[j]*(c[j+1] + 2*c[j])) / 3;
        d[j] = (c[j+1] - c[j]) / (3 * h[j]);
    }
    
    a.pop();
    c.pop();
    return { a: a, b: b, c: c, d: d};
}

function vector2(x, y) {
    this.x = x;
    this.y = y;
    
    this.dot = function(rhs) {
        return this.x * rhs.x + this.y * rhs.y; 
    };
        
    this.normalize = function(a) {
        var d = len(this);
        if (d > 0.0) {
            this.x /= d;
            this.y /= d;
        }
    };

}

function angle_between(a, b) {
    // a.b = |a||b|cos(theta)
    la = len(a);
    lb = len(b);
    return Math.acos(dot(a,b) / (la * lb));
}

function rad_to_deg(a) {
    return 180 * a / Math.PI;
}

function dot(a, b) {
    return a.x * b.x + a.y * b.y;
}

function sub(a, b) {
    return new vector2(a.x - b.x, a.y - b.y);
}

function add(a, b) {
    return new vector2(a.x + b.x, a.y + b.y);
}

function mul(s, a) {
    return new vector2(s * a.x, s * a.y);
}

function len(a) {
    return Math.sqrt(a.x * a.x + a.y * a.y);
}

function normalize(a) {
    var d = len(a);
    if (d > 0.0)
        return new vector2(a.x/d, a.y/d);
    return a;
}

function clamp(v, a, b) {
    return Math.max(a, Math.min(v, b));
}

function rand(a, b) {
    return a + Math.random() * (b - a);
}

// from http://www.shiffman.net/teaching/nature/steering/
function steer(target, boid) {
    var desired = sub(target, boid.pos);
    var d = len(desired);
    if (d > 0) {
        desired.normalize();
        desired = mul(rand(0.80, 1.20) * MAX_SPEED, desired);
        var steer = sub(desired, mul(rand(0.02, 0.04), boid.vel));
        steer.x = clamp(steer.x, -MAX_FORCE, MAX_FORCE);
        steer.y = clamp(steer.y, -MAX_FORCE, MAX_FORCE);
        return steer;
    } else {
        return new vector2(0,0);
    }
}

function boid(x, y, heading) {
    this.pos = new vector2(x,y);
    this.heading = heading;
    this.target = new vector2(x+0, y-10);
    this.vel = new vector2(1,0);
}

var initSpline = function() {
    var path_x = [];
    var path_y = [];
    var path_t = [];
    for (var i = 0; i <= path.length; ++i) {
        path_t[i] = i;
        path_x[i] = path[i%path.length].x;
        path_y[i] = path[i%path.length].y;
    }
    
    coeff_x = calcSpline(path_t, path_x);
    coeff_y = calcSpline(path_t, path_y);
    
    for (var i = 0; i < coeff_x.a.length; ++i) {
        spline_x[i] = makeSpline(coeff_x.a[i], coeff_x.b[i], coeff_x.c[i], coeff_x.d[i], i);
        spline_y[i] = makeSpline(coeff_y.a[i], coeff_y.b[i], coeff_y.c[i], coeff_y.d[i], i);
    }
};

var initWorld = function() {

    initSpline();
    
    var canvas = document.getElementById("myCanvas");
    for (var i = 0; i < NUM_BOIDS; ++i) {
        boids.push(new boid(canvas.width*Math.random(), canvas.height*Math.random(), 3.1415*Math.random()));
    }
};

var drawWorld = function(timestamp) {

    var canvas = document.getElementById("myCanvas");
    var context = canvas.getContext("2d");
    context.clearRect(0, 0, canvas.width, canvas.height);

    drawPath(canvas, context);
    drawSpline(canvas, context);
    drawBoids(canvas, context);
    
    var requestAnimationFrame = window.requestAnimationFrame || window.mozRequestAnimationFrame || window.webkitRequestAnimationFrame || window.msRequestAnimationFrame;
    requestAnimationFrame(drawWorld);
};

var drawSpline = function(canvas, context) {
    context.beginPath();
    context.moveTo(path[0].x, path[0].y);
    var t = 0;
    var NUM_SEGMENTS = 10;
    for (var i = 0; i < coeff_x.a.length; ++i) {
        for (var j = 0; j < NUM_SEGMENTS; ++j) {
            var x = evalSpline(coeff_x.a[i], coeff_x.b[i], coeff_x.c[i], coeff_x.d[i], t, i);
            var y = evalSpline(coeff_y.a[i], coeff_y.b[i], coeff_y.c[i], coeff_y.d[i], t, i);
            t += 1.0 / NUM_SEGMENTS;
            context.lineTo(x, y);
        }
    }
    
    var i = coeff_x.a.length-1;
    var x = evalSpline(coeff_x.a[i], coeff_x.b[i], coeff_x.c[i], coeff_x.d[i], t, i);
    var y = evalSpline(coeff_y.a[i], coeff_y.b[i], coeff_y.c[i], coeff_y.d[i], t, i);
    context.lineTo(x, y);

    context.stroke();
    context.closePath();
};

var drawPath = function(canvas, context) {
    context.beginPath();
    context.lineWidth = path_width;
    context.strokeStyle="#ccc";
    context.moveTo(path[0].x, path[0].y);
    var num = path.length;
    for (var i = 0; i <= num; ++i) {
        context.lineTo(path[(i+1)%num].x, path[(i+1)%num].y);
    }
    context.stroke();
    context.closePath();
    
    context.beginPath();
    context.lineWidth = 2;
    context.strokeStyle="#666";
    context.moveTo(path[0].x, path[0].y);
    for (var i = 0; i <= num; ++i) {
        context.lineTo(path[(i+1)%num].x, path[(i+1)%num].y);
    }
    context.stroke();
    context.closePath();
};

var drawBoids = function(canvas, context) {
    for (var i = 0; i < boids.length; ++i) {
        drawBoid(boids[i], canvas, context);
        
        var x = boids[i].pos.x;
        var y = boids[i].pos.y;
        var pos = new vector2(x,y);
        
        if (useSpline) {
            var idx = -1;
            var min_dist = 100000;
            var min_closest = 0;
            for (var j = 0; j < coeff_x.a.length; ++j) {
            
                // determine closest point on the spline
                var ax = coeff_x.a[j]; var bx = coeff_x.b[j]; var cx = coeff_x.c[j]; var dx = coeff_x.d[j];
                var ay = coeff_y.a[j]; var by = coeff_y.b[j]; var cy = coeff_y.c[j]; var dy = coeff_y.d[j];
    
                var dist = function(t) {
                    // D(t) = (ax+bx*t+cx*t^2+dx*t^3-x)^2 + (ay+by*t+cy*t^2+dy*t^3-y)^2
                    // D'(t) = 2*(3*dy*t^2+2*cy*t+by)*(-y+dy*t^3+cy*t^2+by*t+ay)+2*(3*dx*t^2+2*cx*t+bx)*(-x+dx*t^3+cx*t^2+bx*t+ax)
                    var t2 = t*t;
                    var t3 = t2*t;
                    return 2*(3*dy*t2+2*cy*t+by)*(-y+dy*t3+cy*t2+by*t+ay)+2*(3*dx*t2+2*cx*t+bx)*(-x+dx*t3+cx*t2+bx*t+ax);
                };

                var interval = bracket(dist, 0, 1);
                if (interval.res) {
                    var closest = ridder(dist, interval.x1, interval.x2, 0.001);
                    if (closest >= 0.0 && closest <= 1.0) {
                        var pt_on_spline = new vector2(evalSpline(ax, bx, cx, dx, closest, 0), evalSpline(ay, by, cy, dy, closest, 0));
                        var cand = len(sub(pos, pt_on_spline));
                        if (cand < min_dist) {
                            idx = j;
                            min_dist = cand;
                            min_closest = closest;
                        }
                    }
                }
            }
            //console.log('IDX: ', idx, 'CLOSEST: ', min_closest);
            updateBoidSpline(boids[i], idx, min_closest);
        
        } else {
            // find line segment closest to boid
            var idx = -1;
            var min_dist = 100000;
            for (var j = 0; j < path.length; ++j) {
                var cand = len(sub(boids[i].pos, path[j]));
                if (cand < min_dist) {
                    min_dist = cand;
                    idx = j;
                }
            }
            updateBoid(boids[i], path[idx], path[(idx+1)%path.length], canvas, context);
        }
    }
};

var draw_line = function (a, b, style, context) {
    context.beginPath();
    context.strokeStyle=style;
    context.moveTo(a.x, a.y);
    context.lineTo(b.x, b.y);
    context.stroke();
    context.closePath();
};

var updateBoid = function(boid, p0, p1) {

    var x = boid.pos.x;
    var y = boid.pos.y;
    var heading = boid.heading;

    // path to boid
    if (debugDraw)
        draw_line(p0, new vector2(x, y), "#c00", context);
    
    // prediction
    var vel = normalize(boid.vel);
    var prediction = new vector2(x + 5 * vel.x, y + 5 * vel.y);
    var a = sub(prediction, p0);
    var path_dir = normalize(sub(p1, p0));
    theta = angle_between(a, path_dir);
    if (debugDraw)
        draw_line(new vector2(x, y), prediction, "#00c", context);
    
    // projection on path
    // a.b = |A||B|cos(theta). |B| is 1, so use dot
    var proj = add(mul(dot(a, path_dir), path_dir), p0);
    
    var dist_to_proj = len(sub(prediction, proj));
    if (1 || dist_to_proj > path_width/2) {
        var target = add(proj, mul(20, path_dir));
        var acc = steer(target, boid);
        boid.vel = add(boid.vel, acc);
        boid.pos = add(boid.pos, boid.vel);
    }
    
    var vel_normalized = normalize(boid.vel);
    boid.heading = Math.atan2(vel.x, -vel.y);
    
    // proj on path
    if (debugDraw) {
        draw_line(p0, prediction, "#0c0", context);    
        draw_line(p0, proj, "#0c0", context);    
        draw_line(prediction, proj, "#0c0", context);    
    }
};

var updateBoidSpline = function(boid, idx, closest) {
    var x = boid.pos.x;
    var y = boid.pos.y;
    var heading = boid.heading;
    var pt = new vector2(x, y);

    var ax = coeff_x.a[idx]; var bx = coeff_x.b[idx]; var cx = coeff_x.c[idx]; var dx = coeff_x.d[idx];
    var ay = coeff_y.a[idx]; var by = coeff_y.b[idx]; var cy = coeff_y.c[idx]; var dy = coeff_y.d[idx];
    
    var target = new vector2(
        evalSpline(ax, bx, cx, dx, closest + 0.4, 0),
        evalSpline(ay, by, cy, dy, closest + 0.4, 0));
    var acc = steer(target, boid);
    boid.vel = add(boid.vel, acc);
    boid.pos = add(boid.pos, boid.vel);
    var vel_normalized = normalize(boid.vel);
    boid.heading = Math.atan2(boid.vel.x, -boid.vel.y);
    
    if (debugDraw) {
        var canvas = document.getElementById("myCanvas");
        var context = canvas.getContext("2d");
        var pt_on_spline = new vector2(evalSpline(ax, bx, cx, dx, closest, 0), evalSpline(ay, by, cy, dy, closest, 0));
        draw_line(pt, pt_on_spline, "#0c0", context);
        draw_line(pt, target, "#cc0", context);
    }
}

var onClick = function(event) {
    console.log('onclick');
    path.push(new vector2(event.clientX, event.clientY));
    initSpline();
};

var drawBoid = function(boid, canvas, context) {
    
    var x = boid.pos.x;
    var y = boid.pos.y;
    var heading = boid.heading;
    
    context.save();
    context.translate(x,y);
    context.rotate(heading);
    context.beginPath();
    var top = 0-boid_size*3/2;
    context.moveTo(0, top);
    context.lineTo(0+boid_size*0.7, 0+boid_size);
    context.lineTo(0-boid_size*0.7, 0+boid_size);
    context.lineTo(0, top);
    context.stroke();
    context.closePath();

    context.restore();
};
