<?php

$pages = array('Home', 'Team', 'Results', 'Documentation');

if (isset ($_GET['page'])) { $page = (int) $_GET['page']; }
else { $page=0; }

include('top.inc.php');
?>

<h2>Origin & Objectives</h2>

<p>The <a href="https://sourceforge.net/projects/coqtail/">COQTAIL</a> project is the biological
son of the workpackage `Proofs` of the <a href="http://graal.ens-lyon.fr/coquille">COQUILLE</a> 
project. It is therefore based on all the results obtained during the development of COQUILLE.</p>

<p>In addition to implementing tools dedicated to the easy formalization of mathematics as we see 
them in french <i>Classes préparatoires</i>, this project will proove licence-level results.</p> 

<h2>Development axis</h2>

<ul>
	<li>Analysis (real and complex)</li>
	<li>Arithmetic</li>
	<li>Calculability</li>
	<li><b>C</b> implementation</li>
	<li>Logic and <b>R</b> axiomatic expressivity</li>
	<li>Topology</li>
</ul>

<?php
include('foot_en.inc.php')
?>