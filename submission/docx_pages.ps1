param(
  [Parameter(Mandatory = $true)][string]$Docx,
  [string]$Pdf = ""
)
$ErrorActionPreference = 'Stop'
$word = New-Object -ComObject Word.Application
$word.Visible = $false
$word.DisplayAlerts = 0
try {
  $doc = $word.Documents.Open($Docx, $false, $false)
  if ($Pdf -ne "") {
    $doc.ExportAsFixedFormat($Pdf, 17)   # 17 = wdExportFormatPDF
  }
  $pages = $doc.ComputeStatistics(2)     # 2 = wdStatisticPages
  $doc.Close($false)
  Write-Output $pages
} finally {
  $word.Quit()
  [System.Runtime.Interopservices.Marshal]::ReleaseComObject($word) | Out-Null
}
