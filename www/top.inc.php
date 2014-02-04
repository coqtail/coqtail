<?php
if (isset ($_GET['doc']))
{
  $tmp = htmlspecialchars($_GET['doc']);
  if (file_exists('doc/'.$tmp.'.html')) { $doc = 'doc/'.$tmp.'.html'; }
}

if (! isset ($doc)) { $doc=0; }

echo '<?xml version="1.0" encoding="UTF-8"?>'."\n";
?>
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
    "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="fr">
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
  <meta http-equiv="Content-Style-Type" content="text/css" />
  <link href="main.css" rel="stylesheet" type="text/css" media="all" />
  <link href="doc/coqdoc.css" rel="stylesheet" type="text/css" media="all" />
  <link rel="icon" type="image/png" href="img/favicon.png">
  
  <title>Coqtail - site officiel</title>
  <script type="text/javascript">
    var _gaq = _gaq || [];
    _gaq.push(['_setAccount', 'UA-23791559-1']);
    _gaq.push(['_trackPageview']);
    (function() {
      var ga = document.createElement('script'); ga.type = 'text/javascript'; ga.async = true;
      ga.src = ('https:' == document.location.protocol ? 'https://ssl' : 'http://www') + '.google-analytics.com/ga.js';
      var s = document.getElementsByTagName('script')[0]; s.parentNode.insertBefore(ga, s);
    })();
  </script>
</head>
<?php
if (1326866399 < time() && time() < 1326952800)
{
?>
<body style="background-color:black">
<div style="margin:auto; border:1px solid #FFFFFF; width:500px; color:#FFFFFF; padding:20px">

<p>Le site de Coqtail est temporairement inaccessible en signe d'opposition
à SOPA et PIPA. Plus d'information sur ces lois de censure du net est
disponible <a href="http://fr.wikipedia.org/wiki/Stop_Online_Piracy_Act">ici</a></p>

<p>Coqtail's website is temporarily down in sign of protest against SOPA
and PIPA. For more information on these bills bringing censorship to the
web, one can go <a href="http://en.wikipedia.org/wiki/Stop_Online_Piracy_Act">here</a></p>

</div>
</body>
</html>
<?
}
else
{
?>
<body>
<div id="container">

  <div id="top">
    <div id="left_top">
      <img src="img/coqtail.png" title="Coqtail's logo" width="200" height="200" alt="coqtail's logo" />
    </div>

    <div id="right_top">
      <div id="language">
        <a href=".?<?=$pagename?>/fr"><img src="img/fr.png" title="French" alt="French" /></a>
        <a href=".?<?=$pagename?>/en"><img src="img/gb.png" title="English" alt="English" /></a>
      </div>
      <div id="description"><h1>Coqtail</h1>
        <h2 class="sigle">
          <span class="highlight">COQ</span>
          <span class="highlight">T</span>heorems, 
          <span class="highlight">A</span>bstractions and
          <span class="highlight">I</span>mplementations
          (Bachelor-<span class="highlight">L</span>evel)
        </h2>
      </div>
      <div id="menu">
        <ul><?php echo "\n";
        foreach($tabs as $code)
        {
          if ($code == $pagename) {
            $ext = ' id="current"';
          } else {
            $ext = '';
          }?>
          <li><a<?=$ext?> href=".?<?=$code?>/<?=$lang?>"><?=$aliases[$code]?></a></li><?php echo "\n";
        }

        ?>
        </ul>
    </div>
    </div>
    <div class="clean"></div>
  </div>

  <div id="middle">
<?php
}
?>
