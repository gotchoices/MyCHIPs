
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
          <div class="icon-box">
            <div class="icon"><i class="$1"></i></div>
            <h4 class="title"><a href="$2">$3</a></h4>
            <p class="description">$4</p>
          </div>
        </div>
')
