var page = require('webpage').create(),
    system = require('system'),
    address, output;

if (system.args.length < 3 || system.args.length > 4) {
    console.log('Usage: graphrender.js URL filename [zoom]');
    phantom.exit(1);
} else {
    address = system.args[1];
    output = system.args[2];
    w = 900
    h = 900
    size = 7.5;
    if (system.args.length > 3) {
        scale = system.args[3];
    } else {
        scale = 1;
    }
    if (scale < 1) {
        w = w*scale;
        h = h*scale;
    }
    if (system.args[2].substr(-4) === ".pdf") {
        size = (size*scale) + "in";
        page.paperSize = { width: size, height: size, margin: '0px' };
    }
    page.viewportSize = { width: w, height: h };
    page.zoomFactor = system.args[3];

    //page.content = '<html><body>Create the content here</body></html>';
    page.open(address, function (status) {
        if (status !== 'success') {
            console.log('Build Graph - PhantomJS unable to load the address!');
            phantom.exit();
        } else {
            window.setTimeout(function () {
                //page.render('/dev/stdout', { format: 'png' });
               page.render(output);
               phantom.exit();
            }, 500);
        }
    });
}