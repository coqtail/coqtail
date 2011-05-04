  </div>

  <div id="footer">
   <p id="mentions">
   <br /><a href="http://sourceforge.net/projects/coqtail"><img src="http://sflogo.sourceforge.net/sflogo.php?group_id=298939&amp;type=9" width="80" height="15" alt="Get Coqtail at SourceForge.net. Fast, secure and Free Open Source software downloads" /></a><br />
   <?php
      if($lang=="fr") {
        echo "Dernières modifications : avril 2011";
      } else {
        echo "last modified: April 2011";
      }
    ?>
    </p>
    <p id="w3c">
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
