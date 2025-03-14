
define(GETAPP,`<div class="content_section_text">
        Download the app for your mobile device here:
        <a href="/chark.apk">Android</a>
        or
        <a href="https://testflight.apple.com/join/5IP35ipV">iPhone.</a>
      <p>
        And then try again using the same link that got you here.
      </div>')

define(LINK_BLOCK, `
        <div class="col-md-6 col-lg-4 d-flex align-items-stretch mb-5 mb-lg-50">
          <div class="icon-box" style="padding: 30px 20px;">
            <div class="icon"><i class="$1"></i></div>
            <h4 class="title"><a href="$2">$3</a></h4>
            <p class="description">$4</p>
          </div>
        </div>
')

define(NEWS_BLOCK, `
        <div class="col-md-12 mb-4">
          <div class="card">
            <div class="card-body">
              <h5 class="card-title"><i class="$1"></i> <span class="text-muted">$2</span> $3</h5>
              <p class="card-text">$4</p>
              ifelse(`$5',`',`',`$5')
            </div>
          </div>
        </div>
')

define(SOCIAL_LINK, `
        <div class="col-md-$1">
          <a href="$2" class="btn btn-outline-primary btn-lg" style="width: 80%;">
            <i class="$3"></i> $4
          </a>
        </div>
')
