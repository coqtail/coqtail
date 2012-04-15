  </div>

  <div id="footer">
   <p id="mentions">
   <br /><a href="http://sourceforge.net/projects/coqtail"><img src="http://sflogo.sourceforge.net/sflogo.php?group_id=298939&amp;type=9" width="80" height="15" alt="Get Coqtail at SourceForge.net. Fast, secure and Free Open Source software downloads" /></a><br />
   <?php
      if($lang=="fr") {
        echo "Dernières modifications : avril 2012";
      } else {
        echo "last modified: April 2012";
      }
    ?>
    </p>
    <p id="w3c">
       <a href="http://validator.w3.org/check?uri=referer">
        <img style="border:0;width:88px;height:31px" src="img/valid-xhtml10.png" alt="Valid XHTML 1.0 Strict" title="Valid XHTML 1.0 Strict" height="31" width="88" />
       </a>
       <a href="http://jigsaw.w3.org/css-validator/check/referer">
        <img style="border:0;width:88px;height:31px" src="img/valid-css.png" <?php if($lang=='fr') { $css='CSS Valide !'; } else { $css='Valid CSS!'; } ?> alt="<?=$css?>" title="<?=$css?>" />
       </a>
       <a href="http://www.gnu.org/licenses/lgpl.html">
        <img src="img/lgplv3.png"  <?php if($lang=='fr') { $gpl='Coqtail est un logiciel libre'; } else { $gpl='Coqtail is Free Software'; } ?> alt="<?=$gpl?>" title="<?=$gpl?>" />
       </a>
    </p>
  </div>

</div>
</body>
</html>
