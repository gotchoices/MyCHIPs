// webpack.config.js
//Copyright MyCHIPs.org; See license in root of this package
// -----------------------------------------------------------------------------
const { VueLoaderPlugin } = require('vue-loader')
const { BundleAnalyzerPlugin } = require('webpack-bundle-analyzer')
const webpack = require('webpack')
const path = require('path');
                
const webpackConfig = {
  entry: {
    admin:'./src/admin.js',
    user: './src/user.js',
    report: './src/report.js',
    contract: './src/contract.js',
  },
  output: {
    path: path.join(__dirname, '..', 'pub'),
    filename: '[name]-bundle.js'
  },
  resolve: {
    alias: {
//      vue: '@vue/runtime-dom'
      vue: path.resolve('./node_modules/vue/dist/vue.runtime.esm-bundler.js')	//See: https://github.com/vuejs/vue-cli/issues/4271
//      vue: path.resolve('./node_modules/vue/dist/vue.esm-bundler.js')	//See: https://github.com/fengyuanchen/vue-feather/issues/8
    },
//    mainFields: ['main', 'module']
  },
  plugins: [
    new VueLoaderPlugin(),
    new webpack.DefinePlugin({		// Define Vue feature flags here
      __VUE_OPTIONS_API__: JSON.stringify(true),
      __VUE_PROD_DEVTOOLS__: JSON.stringify(true),
      __VUE_PROD_HYDRATION_MISMATCH_DETAILS__: JSON.stringify(true),
    })
  ],
  performance: {
    maxAssetSize: 2000000,
    maxEntrypointSize: 1000000
  },
  module: {
    rules: [
      {
        test: /\.js$/,
        exclude: /(node_modules|bower_components)/,
        use: {
          loader: 'babel-loader',
          options: {
            presets: ['@babel/preset-env']
          }
        }
      },
      {
        test: /\.vue$/,
        exclude: /(node_modules|bower_components)/,
        use: [ 'vue-loader' ]
      },
      {
        test: /\.(less|css)$/,
        use: [ 'style-loader', 'css-loader', 'less-loader' ],
      },
      {
        test: /\.scss$/,
        use: [ 'style-loader', 'css-loader', 'sass-loader' ],
      },
      {
        test: /.*\.(gif|png|jpe?g)$/i,
        use: [ 'file-loader' ],
      },
      {
        test: /.*\.svg$/i,
        use: [ 'file-loader?name=[path][name].[ext]&context=./lib' ],
      }
    ]
  },
  devServer: {
       port: 3000,
       host: '0.0.0.0', disableHostCheck: true,	//To browse from different host on lan
       hot: true, hotOnly: true,
       contentBase: 'pub'
   }
}

if (process.env.ANALYZE)
  webpackConfig.plugins.push(new BundleAnalyzerPlugin({
    analyzerHost: '0.0.0.0',
    analyzerPort: 8882
  }))

module.exports = webpackConfig
