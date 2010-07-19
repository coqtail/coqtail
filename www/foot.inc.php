  </div>

  <div id="footer">
    <?php
      if($lang=="fr") {
        echo "Dernières modifications : juillet 2010";
      } else {
        echo "last modified: July 2010";
      }
    ?>
    <p>
       <a href="http://validator.w3.org/check?uri=referer"><img
          style="border:0;width:88px;height:31px"
      src="img/valid-xhtml10.png"
          alt="Valid XHTML 1.0 Strict"
          title="Valid XHTML 1.0 Strict"
          height="31" width="88" /></a>
        <a href="http://jigsaw.w3.org/css-validator/check/referer"><img
      style="border:0;width:88px;height:31px"
          src="img/valid-css.png"
          <?php if($lang=='fr') { $css='CSS Valide !'; } else { $css='Valid CSS!'; } ?>
          alt="<?=$css?>"
          title="<?=$css?>"
          /></a>
    </p>
  </div>

</div>
</body>
</html>
