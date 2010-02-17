<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
    "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html xmlns="http://www.w3.org/1999/xhtml" xml:lang="fr">
<head>
	<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
	<meta http-equiv="Content-Style-Type" content="text/css" />
	<link href="main.css" rel="stylesheet" type="text/css" media="all" />

	<title>Coqtail - site officiel</title>

</head>
<body>
<div id="container">

	<div id="top">
		<div id="left_top">
			<img src="img/coqtail.png" title="Coqtail's logo" width="200" height="200" alt="coqtail's logo" />
		</div>
		<div id="right_top">
			<div id="language">
<?php
$ext = '';
if ($_SERVER['QUERY_STRING'] != '')
{
	$ext = '?'.$_SERVER['QUERY_STRING'];
}
?>
				<a href="main.php<?=$ext?>"><img src="img/fr.png" title="French" alt="French" /></a>
				<a href="main_en.php<?=$ext?>"><img src="img/gb.png" title="English" alt="English" /></a>
			</div>
			<div id="description"><h1>Coqtail</h1>
				<h2><span class="highlight">COQ</span> <span class="highlight">T</span>heorems, 
				<span class="highlight">A</span>bstractions and <span class="highlight">I</span>mplementations 
				(<span class="highlight">L</span>icence-level)</h2>
			</div>
			<div id="menu">
				<ul>
<?php

$bound = count ($pages) - 1;
for($i=0; $i <= $bound; $i++)
{
	if ($i == $page) { $ext = ' id="current"'; }
	else { $ext = ''; }
	echo '<li><a href="'.$_SERVER['PHP_SELF'].'?page='.$i.'"'.$ext.'>'.$pages[$i].'</a></li>';
}

?>
				</ul>
		</div>
		</div>
		<div class="clean"></div>
	</div>

	<div id="middle">