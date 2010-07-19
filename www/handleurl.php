<?php
  /** Managing pages */
  $codepages = array("home", "team", "results", "doc");
  $defaultpage = $codepages[0];
    
  /** Get a page by it's number */
  $numpage = -1;
  if (isset($_GET['page'])) {
    $numpage = (int) $_GET['page'];
  }
  
  /** Manage a little bit nicer urls */
  $args = strtolower(implode("/", array_keys($_GET)));
  $keys = preg_split("/[ ._\/\?&,;!§]+/", $args);
  
  // which page?
  $pagename = $defaultpage;
  foreach($codepages as $k) {
    if(in_array($k, $keys)) {
      $pagename = $k;
    }
  }
  //overwriting argument "page=n"
  if($numpage >= 0) $pagename = $codepages[$numpage];
  
  //which language?
  $lang = "fr";
  if(in_array("fr", $keys)) $lang = "fr";
  if(in_array("en", $keys)) $lang = "en";
  if(isset($FORCE_LANG)) $lang = $FORCE_LANG;
  
  if($lang == "fr") {
    $aliases = array(
      'home' => 'Accueil',
      'team' => 'Équipe',
      'results' => 'Résultats',
      'doc' => 'Documentation'
    );
  } else {
    $aliases = array(
      'home' => 'Home',
      'team' => 'Team',
      'results' => 'Results',
      'doc' => 'Documentation'
    );
  }
  
  // RETRO COMPATIBILITY
  $pages = array();
  for($i=0; $i<count($aliases); $i++) {
    $pages[$i] = $aliases[$codepages[$i]];
    if($codepages[$i]==$pagename) {
      $page = $i;
    }
  }
?>
